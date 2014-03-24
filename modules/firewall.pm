package firewall;
use strict;
use warnings;
use File::Basename; 
use Cwd 'abs_path';

BEGIN {
    use Exporter();
    our ($VERSION, @ISA, @EXPORT);
    # set the version for version checking
    $VERSION     = 1.00;
    # if using RCS/CVS, this may be preferred
    $VERSION = sprintf "%d.%03d", q$Revision: 1.0 $ =~ /(\d+)/g;
    @ISA     = qw(Exporter);
    @EXPORT  = qw(
                 check_confs
                 check_conf_syntax
                 init
                 gen
                 gentc
                 flow
                 gen_main_rules
                 finalize
                 add_rules_from_file
                 load_rules_from_file
                 load_rules
                 load_tc_rules
                 generate_save_counters
                );
}

# src.in.out.dst -> chainnames+options
our @items;
our %gv = ();
our $interfaces;
our $networks_filename = '';
our %networks = ();

my %flows_filter = ();
my %flows_mangle = ();
my %filter_flow = (); # инициализирована ли цепочка потока
my %filter_deny = ();
my %filter_skip = ();
my %filter_limit = ();
my %filter_allow = ();
my %filter_count = (); # инициализирована ли цепочка счетчиков
my %filter_jumps2cnt = (); # вставлено ли в цепочку потока правило перехода в цепочку счетчиков

my %mangle_flow = ();
my %mangle_class = ();

my %tc_handles = (); # список последних classid, использованных в комманде tc

my @filter_rules = ();
my @mangle_rules = ();
my @nat_rules = ();
my @raw_rules = ();
my @tc_rules = ();

# globals
my ($def_srcip,$def_dstip) = ('','');
my $ordered_rules = 1; # сортировать ли список головных правил по именам target-цепочек

# const
my $suffix_allow = '_ALLOW';
my $suffix_cnt = '_CNT';
my $suffix_skip = '_SKIP_OR_DENY';
my $suffix_limit = '_LIMIT';
my $suffix_deny = '_DENY';
my $suffix_allow_len = length($suffix_allow);
my $suffix_cnt_len = length($suffix_cnt);
my $suffix_skip_len = length($suffix_skip);
my $suffix_limit_len = length($suffix_limit);
my $suffix_deny_len = length($suffix_deny);
my $cfg_name = 'default';

################################################################################
sub neg
################################################################################
{   # $_[0] - iptables switch, $_[1] - value, -switch ! bla-bla-bla -> ! -switch bla-bla-bla
    return '' if ($_[1]//'') eq '';
    $_[1] =~ /^!\s*(.+)/ ? return '! '.$_[0].' '.$1 : return $_[0].' '.$_[1];
}

################################################################################
sub check_confs
################################################################################
{
    if (@_ == 1) {
        my $cfg_path = $_[0];
        my $filename = '';
        opendir(DIR, $cfg_path) || print "Error in \"$cfg_path\" directory\n";
        foreach my $file ( readdir(DIR) ) {
            $filename = $cfg_path.'/'.$file;
            if ( -f $filename && system("grep -q \"#!/usr/bin/perl\" $filename") == 0) {
                return 1 if check_conf_syntax($filename) != 0;
            }
        }
        closedir(DIR);
        return 0;
    } else {
        print "sub check_confs: no arguments\n";
        exit 1;
    }
}

################################################################################
sub check_conf_syntax
################################################################################
{
    if (@_ == 1) {
        if (system('perl -c '.$_[0]) == 0) {
            return 0;
        } else {
            print "\nSyntax errors in ",$_[0],"!!!\n";
            return 1;
        }
    } else {
        print "sub check_conf_syntax: no arguments\n";
        exit 1;
    }
}

################################################################################
sub init
################################################################################
{
    my ($cfg_name,$networks_name) = @_;
    if (!defined $networks_name) {
        print "Networks filename is undefined\n";
        return 1;
    }
    my $ret = do $networks_name;
    if (defined $ret) {
        $interfaces = get_gateway_ifaces();
        $networks_filename = $networks_name;
        return 0
    } else {
        print "Couldn't run $networks_name\n";
        return 1;
    }
}

################################################################################
sub get_gateway_ifaces
################################################################################
{
    # находим хост и возвращаем ссылку на список его интерфейсов
    foreach my $net (values %networks) {
        if ( $net->{type} eq 'host' ) {
            return $net->{ifaces};
        }
    }
}

################################################################################
sub get_flowopts
################################################################################
{   my ($srcnet, $in, $out, $dstnet) = @_;
    # !!! By design: функция должна находить параметры и в случае если для поиска
    # указаны входящий/исходящий интерфейсы, но в опциях параметры потока специфицированы
    # для пары сетей без уточнения интерфейсов (т.е указанные параметры относятся ко всем
    # потокам м/у двумя сетями через любые интерфейсы)
    my $r = $networks{$srcnet}{flows_options}{$dstnet.(defined $in?'/'.$in:(defined $out?'/':'')).(defined $out?'/'.$out:'')};
    $r = $networks{$srcnet}{flows_options}{$dstnet.(defined $in?'/'.$in:'')} if !defined $r;
    $r = $networks{$srcnet}{flows_options}{$dstnet.(defined $out?'//'.$out:'')} if !defined $r;
    $r = $networks{$srcnet}{flows_options}{$dstnet} if !defined $r;
    return $r;
}

################################################################################
sub get_flows_opts
################################################################################
{ my ($srcnet, $in, $out, $dstnet) = @_;
  my ($filter_chain,$mangle_chain,$cnt_chain_name,$count) = ('','','');

  if (exists $networks{$srcnet}) {
    if (exists $networks{$dstnet}) {
      if (!defined $in || exists $networks{$srcnet}{ifaces}{$in} || /$in/ ~~ %$interfaces) {
        if (!defined $out || exists $networks{$srcnet}{ifaces}{$out} || /$out/ ~~ %$interfaces) {
          my $opts = get_flowopts($srcnet, $in, $out, $dstnet);
          #
          $filter_chain .= $opts->{order}.'_' if exists $opts->{order};
          if (exists $opts->{filter_chain}) {
            $filter_chain .= $opts->{filter_chain};
          } else {
            # !!! By design: интерфейсы игнорируются и трафик между 2-мя
            # сетями проверяется по одной и той же цепочке, независимо от
            # входящих/исходящих интерфейсов.
            # Для детализации по интерфейсам есть опции потоков.
            $filter_chain .= $networks{$srcnet}{name}.'_'.$networks{$dstnet}{name};
          }
          #
          $mangle_chain .= $opts->{order}.'_' if exists $opts->{order};
          if (exists $opts->{mangle_chain}) {
            $mangle_chain .= $opts->{mangle_chain};
          } else { # !!! By design: то же
            $mangle_chain = $filter_chain;
          }
          if (exists $opts->{cnt_chain}) {
            $cnt_chain_name = $opts->{cnt_chain};
          } else {
            $cnt_chain_name .= $filter_chain.$suffix_cnt;
          }
          return {filter_chain => $filter_chain, mangle_chain => $mangle_chain,
                  cnt_chain => $cnt_chain_name, opts => $opts};
        } else { print "Error: interface '$out' in '$dstnet' does not exists\n"; die}
      } else { print "Error: interface '$in' in '$srcnet' does not exists\n"; die}
    } else { print "Error: network or host '$dstnet' does not exists\n"; die}
  } else { print "Error: network or host '$srcnet' does not exists\n"; die}
}

################################################################################
sub get_link_chains
################################################################################
{ my ($srcnet, $in, $out, $dstnet) = @_;
  my %result = ();

  if (exists $networks{$srcnet}) {
    if (exists $networks{$dstnet}) {
      if (!defined $in || exists $networks{$srcnet}{ifaces}{$in} || /$in/ ~~ %$interfaces) {
        if (!defined $out || exists $networks{$dstnet}{ifaces}{$out} || /$out/ ~~ %$interfaces) {
          foreach my $flow (keys %{$networks{$srcnet}{flows_options}}) {
            my ($opt_dstnet,$opt_in,$opt_out) = split('/',$flow);
            # при поиске опций потоков учитываем заданы ли интерфейсы
            if ($opt_dstnet eq $dstnet && (!defined $in || ($in//'') eq ($opt_in//'')) &&
              (!defined $in || ($out//'') eq ($opt_out//''))) {

              my $f = get_flows_opts($srcnet, $opt_in, $opt_out, $opt_dstnet);
              if (defined $f) {
                $result{$f->{filter_chain}}{init} = 1;
                $result{$f->{filter_chain}}{opts} = $f->{opts};
              } else {die};
            }
          }
          return \%result;
        } else { print "Error: interface '$out' in '$dstnet' does not exists\n"; die}
      } else { print "Error: interface '$in' in '$srcnet' does not exists\n"; die}
    } else { print "Error: network or host '$dstnet' does not exists\n"; die}
  } else { print "Error: network or host '$srcnet' does not exists\n"; die}
}

################################################################################
sub update_filter_counters
################################################################################
{
    # $_[0] - имя цепочки в тексте правила
    # $_[1] - выполнять ли инициализацию цепочек
    if (substr($_[0],-$suffix_allow_len,$suffix_allow_len) eq $suffix_allow) {
        my $chain_name = substr($_[0],0,length($_[0]) - $suffix_allow_len);
        init_filter_allow($chain_name) if ! defined $filter_allow{$chain_name} && $_[1];
        $filter_allow{$chain_name}++;
    } elsif (substr($_[0],-$suffix_cnt_len,$suffix_cnt_len) eq $suffix_cnt) {
        my $chain_name = substr($_[0],0,length($_[0]) - $suffix_cnt_len);
        init_filter_cnt($_[0]) if ! defined $filter_count{$chain_name}{count} && $_[1];
        $filter_count{$chain_name}{count}++;
    } elsif (substr($_[0],-$suffix_skip_len,$suffix_skip_len) eq $suffix_skip) {
        my $chain_name = substr($_[0],0,length($_[0]) - $suffix_skip_len);
        init_filter_skip($chain_name) if ! defined $filter_skip{$chain_name} && $_[1];
        $filter_skip{$chain_name}++;
    } elsif (substr($_[0],-$suffix_limit_len,$suffix_limit_len) eq $suffix_limit) {
        my $chain_name = substr($_[0],0,length($_[0]) - $suffix_limit_len);
        init_filter_limit($chain_name) if ! defined $filter_limit{$chain_name} && $_[1];
        $filter_limit{$chain_name}++;
    } elsif (substr($_[0],-$suffix_deny_len,$suffix_deny_len) eq $suffix_deny) {
        my $chain_name = substr($_[0],0,length($_[0]) - $suffix_deny_len);
        init_filter_deny($_[0]) if ! defined $filter_deny{$chain_name} && $_[1];
        $filter_deny{$chain_name}++;
    }
}

################################################################################
sub update_mangle_counters
################################################################################
{ # $_[0] - имя цепочки
  # $_[1] - traget в тексте правила
    if (! defined $mangle_flow{$_[0]}) {
        init_mangle_flow_chain($_[0]);
        $mangle_flow{$_[0]} = 0
    }
    $mangle_class{$_[0]}++ if $_[1]//'' eq 'CLASSIFY';
}

################################################################################
sub gen
################################################################################
{
    # $_[0] - имя таблицы
    # $_[1] - текст добавляемого правила
    my ($chain,$target) = ($1,$2) if $_[1] =~ /^\s*\-[AI\:]\s*([\-_0-9A-z]+)(?:.+\-j\s+([A-z]+))?/;
    if ( $_[0] eq 'filter' ) {
        update_filter_counters($chain,1) if defined $chain;
        push(@filter_rules,$_[1]);
    } elsif ( $_[0] eq 'mangle') {
        update_mangle_counters($chain,$target) if defined $chain;
        push(@mangle_rules,$_[1]);
    } elsif ( $_[0] eq 'nat' ) {
        push(@nat_rules,$_[1]);
    } elsif ( $_[0] eq 'raw' ) {
        push(@raw_rules,$_[1]);
    }
}

################################################################################
sub gentc
################################################################################
{
    # $_[0] - текст команды
    push(@tc_rules,$_[0]);
}

#################################################################################
sub init_link_chains
#################################################################################
{   my ($srcnet, $in, $out, $dstnet) = @_;

    # инициализируем цепочку прямого потока
    my $opts = get_flows_opts($srcnet, $in, $out, $dstnet);
    if (! defined $filter_flow{$opts->{filter_chain}} &&
       (($opts->{opts}{ban}//'') ne 'flow')) {
        gen('filter',"### Init direct chain $opts->{filter_chain}");
        init_filter_flow_chain($opts->{filter_chain});
        $filter_flow{$opts->{filter_chain}} = 1;
    }

    # инициализируем цепочки всех обратных потоков данного линка
    my $lc = get_link_chains($dstnet,$out,$in,$srcnet);
    foreach my $rchain (keys %$lc) {
        if (! defined $filter_flow{$rchain} &&
           (($lc->{$rchain}{opts}{ban}//'') ne 'flow')) {
            gen('filter',"### Init reverse chain $rchain ($opts->{filter_chain})");
            init_filter_flow_chain($rchain);
            $filter_flow{$rchain} = 1;
        }
    }
}

################################################################################
sub init_filter_flow_chain
################################################################################
{  my $chain_name = $_[0];

    gen('filter',":$chain_name - [0:0]");
    gen('filter',"-A $chain_name -m state --state RELATED,ESTABLISHED -j ACCEPT");
}

################################################################################
sub init_mangle_flow_chain
################################################################################
{  my $chain_name = $_[0];

    $mangle_class{$chain_name} = 0;
    gen('mangle',":$chain_name - [0:0]");
}

################################################################################
sub init_filter_cnt
################################################################################
{  my $chain_count = $_[0];

    gen('filter',":$chain_count - [0:0]");

# переходы в цепочки счетчиков добавляется в финале, чтобы унифицировать
# инициализацию цепочек для сгенерированных и добавленных из файлов правил
#    gen('filter',"-I $chain_name 1 -j $cnt_chain");
#    $filter_jumps2cnt{$chain_name} = 1;
}

################################################################################
sub init_filter_deny
################################################################################
{  my $chain_deny = $_[0];

    gen('filter',":$chain_deny - [0:0]");
}

################################################################################
sub init_filter_skip
################################################################################
{  my $chain_name = $_[0];

    gen('filter',":$chain_name$suffix_skip - [0:0]");
    my $index = ! defined $filter_count{$chain_name} ? 1 : 2;
    gen('filter',"-I $chain_name $index -j $chain_name$suffix_skip");
}

################################################################################
sub init_filter_limit
################################################################################
{  my $chain_name = $_[0];

    gen('filter',":$chain_name$suffix_limit - [0:0]");
    my $index = 2;
    if (defined $filter_count{$chain_name} && defined $filter_skip{$chain_name}) {
        # есть цепочки счетчиков и исключений + ACCEPT RELATED
        $index = 3;
    } elsif (! defined $filter_count{$chain_name} && ! defined $filter_skip{$chain_name}) {
        # нет цепочек счетчиков и исключений + ACCEPT RELATED
        $index = 1;
    } # иначе есть какая-то одна из двух цепочек + ACCEPT RELATED - вставляем третьей
    gen('filter',"-I $chain_name $index -j $chain_name$suffix_limit");
}

################################################################################
sub init_filter_allow
################################################################################
{  my $chain_name = $_[0];

    gen('filter',":$chain_name$suffix_allow - [0:0]");
}

################################################################################
sub flow
################################################################################
{  my ($cfg_file,$flows_list) = @_;

    # строим хэш для дальнейшего быстрого выяснения подходит ли обрабатываемое
    # правило под заданный в параметрах список потоков ($flow_list)
    my %flows2parse = ();
    if ( defined $flows_list ) {
        foreach (@{$flows_list}) {
            $flows2parse{($_->[0]//'').'/'.($_->[1]//'').'/'.
                         ($_->[2]//'').'/'.($_->[3]//'')} = 1; # initialized
        }
    }

    @items = ();
    my $ret = do $cfg_file;
    if (!defined $ret) {
        print "Error: couldn't run $cfg_file\n";
        return 1;
    }

    print "  Config file is $cfg_file\n";
    if (defined $flows_list) {
        foreach (@{$flows_list}) {
            print "    Setting up ",$_->[0]," -> ",$_->[3], " rules... \n";
        }
    };
    foreach my $item (@items) {
        my $firsttime = 1;
        foreach my $rule (@{$item->{rules}}) {
            if (! %flows2parse or
                exists $flows2parse{$rule->{srcnet}.'///'.$rule->{dstnet}} or
                exists $flows2parse{$rule->{srcnet}.'/'.
                        ($rule->{in}//'').'//'.$rule->{dstnet}} or
                exists $flows2parse{$rule->{srcnet}.'//'.
                        ($rule->{out}//'').'/'.$rule->{dstnet}} or
                exists $flows2parse{$rule->{srcnet}.'/'.($rule->{in}//'').'/'.
                        ($rule->{out}//'').'/'.$rule->{dstnet}}) {
                print "    Setting up rules for: ",$item->{name}, "\n" if $firsttime;
                process_ruleset($item, $rule);
                $firsttime = 0;
            }
        }
    }
    return 0;
}

################################################################################
sub process_ruleset
################################################################################
{
    my ($item,$rule) = @_;

    my $srcnet = $rule->{srcnet};
    my $in     = $rule->{in};
    my $out    = $rule->{out};
    my $dstnet = $rule->{dstnet};

    ($def_srcip,$def_dstip) = ('','');
    # определяем ip-адреса если для данного правила
    # ip-адреса не заданы, но задан адрес для узла, используем его
    # (это чтобы можно было не писать в каждом правиле ip-адрес узла, когда это удобно)
    if ( defined $rule->{srcip} ) {
        $def_srcip  = $rule->{srcip};
    } else {
        $def_srcip  = $item->{ipv4} if defined $item->{ipv4} && $item->{net} eq $srcnet;
    }
    if ( defined $rule->{dstip} ) {
        $def_dstip  = $rule->{dstip};
    } else {
        $def_dstip  = $item->{ipv4} if defined $item->{ipv4} && $item->{net} eq $dstnet;
    }

    my $dchains = get_flows_opts($srcnet, $in, $out, $dstnet);
    my $rchains = get_flows_opts($dstnet, $out, $in, $srcnet);

    if (defined $dchains && defined $rchains) {
        if (($dchains->{opts}{ban}//'') ne 'flow') {

            init_link_chains($srcnet, $in, $out, $dstnet);
            if (($dchains->{opts}{ban}//'') ne 'rules') {
                process_pre_rules($rule,$dchains);
                process_deny($rule,$dchains);
                process_limit($rule,$dchains);
                process_allow($rule,$dchains,$rchains);
                process_speed($rule,$dchains,$rchains);
                process_classify($rule,$dchains);
            } else {
                print 'Warning: rules for flow ',$srcnet,'->',(defined $in?$in.'->':''),
                (defined $out?$out.'->':''),$dstnet," completely forbidden in '$networks_filename'!!!\n"}
        } else {
            print 'Warning: flow ',$srcnet,'->',(defined $in?$in.'->':''),
            (defined $out?$out.'->':''),$dstnet," is explicitly forbidden in '$networks_filename'!!!\n"}
    } else {
        print 'Warning: flow ',$srcnet,'->',(defined $in?$in.'->':''),
        (defined $out?$out.'->':''),$dstnet," not found in '$networks_filename'!!!\n"}

}

################################################################################
sub process_pre_rules
################################################################################
{  my ($rule,$dchains,$rchains) = @_;

    foreach my $pre_rule (@{$rule->{pre_rules}}) {
        if (defined $pre_rule->{rule}) {
            gen('filter','-A '.$pre_rule->{rule});
        }
    }
}

################################################################################
sub process_deny
################################################################################
{  my ($rule,$dchains) = @_;

    foreach my $deny (@{$rule->{deny}}) {
        my ($deny_srcip,$deny_dstip,$deny_proto,$deny_sport,$deny_dport,$deny_tcp_flags) = ('','','','','','',''); 
        $deny_srcip = neg('-s',$def_srcip) if $def_srcip ne '';
        $deny_dstip = neg('-d',$deny->{dstip}) if defined $deny->{dstip};
        $deny_dstip = neg('-d',$def_dstip) if $def_dstip ne '';
        $deny_proto = neg('-p',$deny->{proto}) if defined $deny->{proto};
        $deny_sport = neg('--sport',$deny->{sport}) if defined $deny->{proto} and defined $deny->{sport};
        $deny_dport = neg('--dport',$deny->{dport}) if defined $deny->{proto} and defined $deny->{dport};
        $deny_tcp_flags = neg('--tcp-flags',$deny->{tcp_flags}) if defined $deny->{proto} and $deny->{proto} eq "tcp" and defined $deny->{tcp_flags};

        # insert LOG before DROP
        if (defined $deny->{'log-prefix'} && $deny->{'limit'} && $deny->{'limit-burst'}) {
            my $log = '--log-prefix '.$deny->{'log-prefix'}.
                ' -m limit --limit '.$deny->{'limit'}.
                ' --limit-burst '.$deny->{'limit-burst'};
            gen('filter',"-A $dchains->{filter_chain}$suffix_deny $deny_proto $deny_srcip $deny_dstip $deny_sport $deny_dport $deny_tcp_flags -j LOG $log");
        }
        gen('filter',"-A $dchains->{filter_chain}$suffix_deny $deny_proto $deny_srcip $deny_dstip $deny_sport $deny_dport $deny_tcp_flags -j DROP");

        # exclude #######################
        foreach my $exclude (@{$deny->{exclude}}) {
            my ($ex_srcip,$ex_dstip,$ex_proto,$ex_dport) = ('','','',''); 
            $ex_srcip = neg('-s',$exclude->{srcip}) if $exclude->{srcip};
            $ex_dstip = neg('-d',$exclude->{dstip}) if $exclude->{dstip};
            $ex_proto = neg('-p',$exclude->{proto}) if $exclude->{proto};
            $ex_dport = neg('--dport',$exclude->{dport}) if defined $exclude->{proto} and defined $exclude->{dport};
            $ex_dstip = $deny_dstip if not defined $exclude->{dstip};
            $ex_proto = $deny_proto if not defined $exclude->{proto};
            $ex_dport = $deny_dport if not (defined $exclude->{proto} and defined $exclude->{dport});
            gen('filter',"-A $dchains->{filter_chain}$suffix_skip $ex_proto $ex_srcip $ex_dstip $ex_dport -j RETURN");
        }
    }
}

################################################################################
sub process_limit
################################################################################
{  my ($rule,$dchains) = @_;

    foreach my $limit (@{$rule->{limit}}) {
        my ($limit_srcip,$limit_dstip,$limit_proto,$limit_sport,$limit_dport,$limit_tcp_flags) = ('','','','','','',''); 
        $limit_srcip = neg('-s',$def_srcip) if $def_srcip ne '';
        $limit_dstip = neg('-d',$limit->{dstip}) if defined $limit->{dstip};
        $limit_proto = neg('-p',$limit->{proto}) if defined $limit->{proto};
        $limit_sport = neg('--sport',$limit->{sport}) if defined $limit->{proto} and defined $limit->{sport};
        $limit_dport = neg('--dport',$limit->{dport}) if defined $limit->{proto} and defined $limit->{dport};
        $limit_tcp_flags = neg("--tcp-flags ",$limit->{tcp_flags}) if defined $limit->{proto} and $limit->{proto} eq "tcp" and defined $limit->{tcp_flags};
        # hashlimit
        my $hashlimit_str = '';
        my $loglimit_str = '';
        my ($loglimit,$loglimit_burst,$log_prefix) = ('','','');
        if ( defined $limit->{'hashlimit'} ) {
            $hashlimit_str  = '-m hashlimit --hashlimit '.$limit->{'hashlimit'};
            $hashlimit_str .= ' --hashlimit-burst '.$limit->{'hashlimit-burst'} if defined $limit->{'hashlimit-burst'};
            $hashlimit_str .= ' --hashlimit-mode '.$limit->{'hashlimit-mode'} if defined $limit->{'hashlimit-mode'};
            $hashlimit_str .= ' --hashlimit-name '.$limit->{'hashlimit-name'} if defined $limit->{'hashlimit-name'};
            $loglimit       = '-m limit --limit '.$limit->{'loglimit'} if defined $limit->{'loglimit'};
            $loglimit_burst = '--limit-burst '.$limit->{'loglimit-burst'} if defined $limit->{'loglimit-burst'};
            $log_prefix     = '--log-prefix "'.$limit->{'log-prefix'}.'"' if defined $limit->{'log-prefix'};
        }
        gen('filter',"-A $dchains->{filter_chain}$suffix_limit $limit_proto $limit_srcip $limit_dstip $limit_sport $limit_dport $limit_tcp_flags -m state --state NEW $hashlimit_str -j RETURN");
        gen('filter',"-A $dchains->{filter_chain}$suffix_limit $limit_proto $limit_srcip $limit_dstip $limit_sport $limit_dport $limit_tcp_flags -m state --state NEW $loglimit $loglimit_burst -j LOG $log_prefix");
        gen('filter',"-A $dchains->{filter_chain}$suffix_limit $limit_proto $limit_srcip $limit_dstip $limit_sport $limit_dport $limit_tcp_flags -m state --state NEW -j DROP");
    }
}

################################################################################
sub process_allow
################################################################################
{  my ($rule,$dchains,$rchains) = @_;

    foreach my $allow (@{$rule->{allow}}) {
        my ($allow_srcip,$allow_dstip,$allow_proto,$allow_sport,$allow_dport,$allow_tcp_flags) = ('','','','','','',''); 
        if (defined $allow->{rule}) {
            gen('filter','-A '.$dchains->{filter_chain}.$suffix_allow.' '.$allow->{rule});
        } else {
            $allow_srcip = neg('-s',$allow->{srcip}//$def_srcip);
            print '>>> Warning: srcip ',$def_srcip,' reassigned to ',$allow->{srcip}," !\n"
                if defined $allow->{srcip} and $def_srcip ne '';

            $allow_dstip = neg('-d',$allow->{dstip}//$def_dstip);
            print '>>> Warning: dstip ',$def_dstip,' reassigned to ',$allow->{dstip}," !\n"
                if defined $allow->{dstip} and $def_dstip ne '';

            $allow_proto = neg('-p',$allow->{proto}) if defined $allow->{proto};
            $allow_sport = neg('--sport',$allow->{sport}) if defined $allow->{proto} and defined $allow->{sport};
            $allow_dport = neg('--dport',$allow->{dport}) if defined $allow->{proto} and defined $allow->{dport};
            $allow_tcp_flags = neg('--tcp-flags',$allow->{tcp_flags}) if defined $allow->{proto} and $allow->{proto} eq "tcp" and defined $allow->{tcp_flags};
            # hashlimit
            my $hashlimit_str = '';
            if ( defined $allow->{'hashlimit'} ) {
                $hashlimit_str = '-m hashlimit --hashlimit '.$allow->{'hashlimit'};
                $hashlimit_str .= ' --hashlimit-burst '.$allow->{'hashlimit-burst'} if defined $allow->{'hashlimit-burst'};
                $hashlimit_str .= ' --hashlimit-mode '.$allow->{'hashlimit-mode'} if defined $allow->{'hashlimit-mode'};
                $hashlimit_str .= ' --hashlimit-name '.$allow->{'hashlimit-name'} if defined $allow->{'hashlimit-name'};
            }
            gen('filter','-A '.$dchains->{filter_chain}.$suffix_allow." $allow_proto $allow_srcip $allow_dstip $allow_sport $allow_dport $allow_tcp_flags -m state --state NEW $hashlimit_str -j ACCEPT");
            # loglimit for hashlimit
            if ( defined $allow->{'hashlimit'} && defined $allow->{'loglimit'} and defined $allow->{'log-prefix'} ) {
                my ($loglimit,$loglimit_burst,$log_prefix) = ('','','');
                $loglimit       = '-m limit --limit '.$allow->{'loglimit'} if defined $allow->{'loglimit'};
                $loglimit_burst = '--limit-burst '.$allow->{'loglimit-burst'} if defined $allow->{'loglimit-burst'};
                $log_prefix     = '--log-prefix "'.$allow->{'log-prefix'}.'"' if defined $allow->{'log-prefix'};
                gen('filter','-A '.$dchains->{filter_chain}.$suffix_allow." $allow_proto $allow_srcip $allow_dstip $allow_sport $allow_dport -m state $allow_tcp_flags --state NEW $loglimit $loglimit_burst -j LOG $log_prefix");
            }
            # counters
            if (defined $dchains->{opts}{count} &&
               ($dchains->{opts}{count} eq 'direct' || $dchains->{opts}{count} eq 'both')) {
                my ($cnt_src,$cnt_sport,$cnt_dst,$cnt_dport) = ('','','','');
                $cnt_src = neg('-s',$def_srcip) if $def_srcip ne '';
                $cnt_dst = neg('-d',$def_dstip) if $def_dstip ne '';
                $cnt_dst = neg('-d',$allow->{dstip}) if defined $allow->{dstip};
                $cnt_sport = neg('--sport',$allow->{sport}) if defined $allow->{proto} and defined $allow->{sport};
                $cnt_dport = neg('--dport',$allow->{dport}) if defined $allow->{proto} and defined $allow->{dport};
                gen('filter',"-A $dchains->{cnt_chain} $allow_proto $cnt_src $cnt_dst $cnt_sport $cnt_dport");
            }
            if (defined $dchains->{opts}{count} &&
               ($dchains->{opts}{count} eq 'back' || $dchains->{opts}{count} eq 'both')) {
                my ($cnt_src,$cnt_sport,$cnt_dst,$cnt_dport) = ('','','','');
                $cnt_dst = neg('-d',$def_srcip) if $def_srcip ne '';
                $cnt_src = neg('-s',$def_dstip) if $def_dstip ne '';
                $cnt_src = neg('-s',$allow->{dstip}) if defined $allow->{dstip};
                $cnt_sport = neg('--sport',$allow->{dport}) if defined $allow->{proto} and defined $allow->{dport};
                $cnt_dport = neg('--dport',$allow->{sport}) if defined $allow->{proto} and defined $allow->{sport};
                gen('filter',"-A $rchains->{cnt_chain} $allow_proto $cnt_src $cnt_dst $cnt_sport $cnt_dport");
            }
        }
    }
}

################################################################################
sub get_tc_iface
################################################################################
{  my ($net, $iface) = @_;

    if (defined $iface) {
        # ищем нитерфейс на котором происходит управление трафиком
        return $interfaces->{$iface}{tc_iface}//$iface;
    } else {
        # если поток идентифицрован только именами сетей то
        # проверяем все ли интерфейсы сети используют один и тот же интерфейс для
        # traffic control
        my $ti;
        foreach my $if (keys %{$networks{$net}{ifaces}}) {
            if (!defined $ti) {
                $ti = $interfaces->{$if}{tc_iface}//$if;# запоминаем первый интерфейс
            } elsif ($ti ne $interfaces->{$if}{tc_iface}//$if) {
                print 'For the interfaces in \''.$net."\' network different traffic control interfaces specified!\n";
                return undef;
            }
        }
        return $ti;
    }
}

################################################################################
sub process_speed
################################################################################
{  my ($rule,$dchains,$rchains) = @_;

    # speed #############################
    foreach my $speed (@{$rule->{speed}}) {
        my ($cn,$s_dir,$s_srcip,$s_dstip,$s_proto,$s_sport,$s_dport,
            $s_iface,$s_down_rate,$s_down_ceil,$s_qdiscid,$s_parent,
            $s_classid,$s_tcp_flags,$s_other) =
            ('','','','','','','','','','','','','','','',''); 
        $s_dir   = $speed->{dir};
        $s_proto = neg('-p',$speed->{proto}) if defined $speed->{proto};
        $s_sport = neg('--sport',$speed->{sport}) if defined $speed->{proto} and defined $speed->{sport};
        $s_dport = neg('--dport',$speed->{dport}) if defined $speed->{proto} and defined $speed->{dport};
        $s_tcp_flags = neg('--tcp-flags',$speed->{tcp_flags}) if defined $speed->{proto} and $speed->{proto} eq "tcp" and defined $speed->{tcp_flags};
        $s_down_rate = $speed->{rate};
        $s_down_ceil = $speed->{ceil};
        $s_other = $speed->{other} if defined $speed->{other} and defined $speed->{other};
        $cn = $dchains->{mangle_chain};
        my $class = 1;
        if ( $s_dir eq 'down' ) {
            if (defined $speed->{out}) {
                $s_iface = $speed->{out};
            } elsif ( !defined ($s_iface = get_tc_iface($rule->{srcnet},$rule->{in}))) {
                print 'There is more then one interface for \''.$rule->{srcnet}.
                    '\' network so it\'s impossible to automatically select '.
                    "interface for traffic control and it must be specified manually!\n";
                return;
            }
            $cn = $rchains->{mangle_chain};
            $s_qdiscid   = $interfaces->{$s_iface}{tc_root_handle};
            $s_dstip = neg('-d',$def_srcip) if $def_srcip ne '';
            $s_srcip = neg('-s',$speed->{srcip}) if defined $speed->{srcip};
        } else { # 'up'
            if (defined $speed->{in}) {
                $s_iface = $speed->{in};
            } elsif ( !defined ($s_iface = get_tc_iface($rule->{dstnet},$rule->{out}))) {
                print 'There is more then one interface for \''.$rule->{dstnet}.
                    '\' network so it\'s impossible to automatically select '.
                    "interface for traffic control and it must be specified manually!\n";
                return;
            }
            $cn = $dchains->{mangle_chain};
            $s_qdiscid   = $interfaces->{$s_iface}{tc_root_handle};
            $s_dstip = neg('-d',$speed->{srcip}) if defined $speed->{srcip};
            $s_srcip = neg('-s',$def_srcip) if $def_srcip ne '';
            if ( ! exists $interfaces->{$s_iface} ) {
                print "Warning: $s_iface is not configured!\n";
                return;
            }
        }
        if (defined $speed->{parent})  {$s_parent = $speed->{parent}} else {$s_parent = "$s_qdiscid:1"}
        # ведем список последних использованных classid для каждого qdiscid
        # и используем эти значения в команде tc
        if (!defined $tc_handles{$s_qdiscid}) {
            $tc_handles{$s_qdiscid} = hex ($interfaces->{$s_iface}{qd_start_minor} // 1);
        }
        if (defined $speed->{classid}) {
            $s_classid = $speed->{classid};
            (my $major, $tc_handles{$s_qdiscid}) = split(/:/,$s_classid);
        } else {
            $s_classid = "$s_qdiscid:".sprintf("%x", $tc_handles{$s_qdiscid})
        }
        $tc_handles{$s_qdiscid}++;
        print "                 classid $s_classid, rate $s_down_rate ceil $s_down_ceil\n";
        gen('mangle',"-A $cn $s_proto $s_srcip $s_dstip $s_sport $s_dport $s_tcp_flags -j CLASSIFY --set-class $s_classid")
            if !defined $speed->{script};
        gentc("tc class replace dev $s_iface parent $s_parent classid $s_classid htb rate $s_down_rate ceil $s_down_ceil $s_other >/dev/null 2>&1");

        ### call script
        if (defined $speed->{script}) {
                no strict;
                # вызываем процедуру по имени
                $speed->{script}->({tch => \%tc_handles, cn => $cn, dir => $s_dir,
                    srcip => $s_srcip, dstip => $s_dstip, proto => $s_proto,
                    sport => $s_sport, dport => $s_dport, iface => $s_iface,
                    down_rate => $s_down_rate, down_ceil => $s_down_ceil,
                    qdiscid => $s_qdiscid, parent => $s_parent,
                    classid => $s_classid, tcp_flags => $s_tcp_flags,
                    other => $s_other, rule => $rule});
                use strict;
        }
    }
}

################################################################################
sub process_classify
################################################################################
{  my ($rule,$dchains,$rchains) = @_;

    foreach my $classify_rule (@{$rule->{classify}}) {
        if (defined $classify_rule->{rule}) {
            gen('mangle',"-A $dchains->{mangle_chain} ".$classify_rule->{rule});
        }
        ### call script
        if (defined $classify_rule->{script}) {
                no strict;
                # вызываем процедуру по имени
                $classify_rule->{script}->({cn => $dchains->{mangle_chain},rule => $rule},
                    $classify_rule->{params});
                use strict;
        }
    }
}

################################################################################
sub gen_flow_rule
################################################################################
{  my ($srcnet,$in,$out,$dstnet,$srcaddr,$dstaddr,$main_chain,$table) = @_;

    my ($in_sw,$out_sw,$fm_chain) = ('','','');
    my $IFO_order = $main_chain eq 'INPUT' ? '1': ($main_chain eq 'FORWARD' ? '2':'3');
    my $opts = get_flows_opts($srcnet,$in,$out,$dstnet);
    if (($opts->{opts}{ban}//'') ne 'flow') {
        if (($table eq 'filter' && $filter_flow{$opts->{filter_chain}}//0 == 1) ||
            ($table eq 'mangle' && defined $mangle_class{$opts->{mangle_chain}})) {
            # убираем часть алиаса интерфейса после ":" (для iptables алиас не значим)
            if (defined $in) {
                $in =~ s/\:[0-9]*//;
                $in_sw = ' -i '.$in;
            }
            if (defined $out) {
                $out =~ s/\:[0-9]*//;
                $out_sw = ' -o '.$out;
            }
            $fm_chain = $table eq 'filter' ? 'filter_chain': 'mangle_chain';
            my $rule = $main_chain.$in_sw.$out_sw.' '.
                neg('-s',$srcaddr).' '.neg('-d',$dstaddr).' -j '.$opts->{$fm_chain};
            if ($ordered_rules) {
                if ($table eq 'filter') {
                    $flows_filter{$srcnet.$in_sw.$out_sw.$dstnet}{order} =
                    $IFO_order.$opts->{$fm_chain}.$in_sw.$out_sw;
                    $flows_filter{$srcnet.$in_sw.$out_sw.$dstnet}{rule} = $rule;
                } else {
                    $flows_mangle{$srcnet.$in_sw.$out_sw.$dstnet}{order} =
                    $IFO_order.$opts->{$fm_chain}.$in_sw.$out_sw;
                    $flows_mangle{$srcnet.$in_sw.$out_sw.$dstnet}{rule} = $rule;
                }
            } else {
                gen($table,'-A '.$rule);
            }
        }
    }
}

################################################################################
sub build_main_rules
################################################################################
{ #my $table = $_[0];

  foreach my $srcnet (keys %networks) {
    foreach my $dstnet (keys %networks) {
      if ( $srcnet ne $dstnet ) {
        my $src = $networks{$srcnet};
        my $dst = $networks{$dstnet};
        if ($src->{type} eq 'net' && $dst->{type} eq 'net') {
          foreach my $in (keys %{$src->{ifaces}}) {
            foreach my $out (keys %{$dst->{ifaces}}) {
              if ($in ne $out) {
                gen_flow_rule($srcnet, $in, $out, $dstnet,
                    $src->{ifaces}{$in}{addr},$dst->{ifaces}{$out}{addr},'FORWARD','filter');
                gen_flow_rule($srcnet, $in, $out, $dstnet,
                    $src->{ifaces}{$in}{addr},$dst->{ifaces}{$out}{addr},'FORWARD','mangle');
              }
            }
          }
        } elsif ($src->{type} eq 'net' && $dst->{type} eq 'host') {
          foreach my $in (keys %{$src->{ifaces}}) {
            gen_flow_rule($srcnet, $in, undef, $dstnet,
              $src->{ifaces}{$in}{addr},$dst->{ifaces}{$in}{addr},'INPUT','filter');
            gen_flow_rule($srcnet, $in, undef, $dstnet,
              $src->{ifaces}{$in}{addr},$dst->{ifaces}{$in}{addr},'INPUT','mangle');
          }
        } elsif ($src->{type} eq 'host' && $dst->{type} eq 'net') {
          foreach my $out (keys %{$dst->{ifaces}}) {
            gen_flow_rule($srcnet, undef, $out, $dstnet,
              $src->{ifaces}{$out}{addr},$dst->{ifaces}{$out}{addr},'OUTPUT','filter');
            gen_flow_rule($srcnet, undef, $out, $dstnet,
              $src->{ifaces}{$out}{addr},$dst->{ifaces}{$out}{addr},'OUTPUT','mangle');
          }
        }
      }
    }
  }
}

################################################################################
sub main_filter_rules
################################################################################
{
    gen('filter',"########################");
    gen('filter',"# filter main rules");
    gen('filter',"########################");
    gen('filter','-F INPUT');
    gen('filter','-F FORWARD');
    gen('filter','-F OUTPUT');

    gen('filter','-A INPUT  -i lo -j ACCEPT');
    gen('filter','-A OUTPUT -o lo -j ACCEPT');

    if ($ordered_rules) {
      foreach my $k (sort {$flows_filter{$a}{order} cmp $flows_filter{$b}{order}} keys %flows_filter) {
        gen('filter','-A '.$flows_filter{$k}{rule});
      }
    }
}

################################################################################
sub main_mangle_rules
################################################################################
{
    gen('mangle',"########################");
    gen('mangle',"# mangle main rules");
    gen('mangle',"########################");

    if ($ordered_rules) {
        foreach my $k (sort {$flows_mangle{$a}{order} cmp $flows_mangle{$b}{order}}
                       keys %flows_mangle) {
            gen('mangle','-A '.$flows_mangle{$k}{rule});
        }
    }
}

################################################################################
sub seal_chains
################################################################################
{
    foreach my $key (keys %filter_deny) {
        if ($filter_deny{$key} != 0) {
            gen('filter',"-A $key$suffix_skip -j $key$suffix_deny");
        }
    }
    foreach my $key (sort keys %filter_flow) {
        if (defined $filter_allow{$key} && $filter_allow{$key} > 0) {
           gen('filter',"-A $key -j $key$suffix_allow");
        }
    }
    # DROP-правила в цепочках потоков должны быть последними
    foreach my $key (sort keys %filter_flow) {
        if (defined $filter_flow{$key} && $filter_flow{$key} == 1) {
            gen('filter',"-A $key -j DROP");
        }
    }
}

################################################################################
sub insert_cntjump
################################################################################
{   my ($srcnet, $in, $out, $dstnet) = @_;

    my $chains = get_flows_opts($srcnet, $in, $out, $dstnet);
    # генерируем только для цепочек, которые создавали и в которых еще нет переходов
    if (defined $filter_count{$chains->{filter_chain}} &&
        !defined $filter_jumps2cnt{$chains->{filter_chain}}) {
        gen('filter',"-I $chains->{filter_chain} 1 -j $chains->{cnt_chain}");
        $filter_jumps2cnt{$chains->{filter_chain}} = 1;
        # учитываем прыжок в цепочку счетчиков в списке
        $filter_count{$chains->{filter_chain}}{cnt_chain} = $chains->{cnt_chain};
    }
}

################################################################################
sub insert_jumps2cnt
################################################################################
{
  foreach my $srcnet (keys %networks) {
    foreach my $dstnet (keys %networks) {
      if ( $srcnet ne $dstnet ) {
        my $src = $networks{$srcnet};
        my $dst = $networks{$dstnet};
        if ($src->{type} eq 'net' && $dst->{type} eq 'net') {
          foreach my $in (keys %{$src->{ifaces}}) {
            foreach my $out (keys %{$dst->{ifaces}}) {
                insert_cntjump($srcnet, $in, $out, $dstnet);
            }
          }
        } elsif ($src->{type} eq 'net' && $dst->{type} eq 'host') {
          foreach my $in (keys %{$src->{ifaces}}) {
            insert_cntjump($srcnet, $in, undef, $dstnet);
          }
        } elsif ($src->{type} eq 'host' && $dst->{type} eq 'net') {
          foreach my $out (keys %{$dst->{ifaces}}) {
            insert_cntjump($srcnet, undef, $out, $dstnet);
          }
        }
      }
    }
  }
}

################################################################################
sub gen_links
################################################################################
{   my $proc = $_[0];

    foreach my $srcnet (keys %networks) {
        foreach my $dstnet (keys %networks) {
            if ( $srcnet ne $dstnet ) {
                my $src = $networks{$srcnet};
                my $dst = $networks{$dstnet};
                if ($src->{type} eq 'net' && $dst->{type} eq 'net') {
                    foreach my $in (keys %{$src->{ifaces}}) {
                        foreach my $out (keys %{$dst->{ifaces}}) {
                            insert_cntjump($srcnet, $in, $out, $dstnet);
                        }
                    }
                } elsif ($src->{type} eq 'net' && $dst->{type} eq 'host') {
                    foreach my $in (keys %{$src->{ifaces}}) {
                        insert_cntjump($srcnet, $in, undef, $dstnet);
                    }
                } elsif ($src->{type} eq 'host' && $dst->{type} eq 'net') {
                    foreach my $out (keys %{$dst->{ifaces}}) {
                        insert_cntjump($srcnet, undef, $out, $dstnet);
                    }
                }
            }
        }
    }
}

################################################################################
sub insert_explicitjumps2cnt
################################################################################
{
  foreach my $srcnet (keys %networks) {
    if (defined $networks{$srcnet}{flows_options}) {
      foreach my $flow (keys %{$networks{$srcnet}{flows_options}}) {
        my ($opt_dstnet,$opt_in,$opt_out) = split('/',$flow);
        if (defined $networks{$srcnet}{flows_options}{$flow}{cnt_chain}) {
          my $chains = get_flows_opts($srcnet, $opt_in, $opt_out, $opt_dstnet);
          # генерируем только для цепочек, которые создавали и в которых еще нет переходов
          if ($filter_flow{$chains->{filter_chain}}//0 == 1 && !defined $filter_jumps2cnt{$chains->{filter_chain}}) {
            gen('filter',"-I $chains->{filter_chain} 1 -j $networks{$srcnet}{flows_options}{$flow}{cnt_chain}");
            $filter_jumps2cnt{$chains->{filter_chain}} = 1;
            # учитываем прыжок в цепочку счетчиков в списке
            $filter_count{$chains->{filter_chain}}{cnt_chain} = $networks{$srcnet}{flows_options}{$flow}{cnt_chain};
          }
        }
      }
    }
  }
}

################################################################################
sub gen_main_rules
################################################################################
{
    build_main_rules;
    main_filter_rules;
    main_mangle_rules;
}

################################################################################
sub finalize
################################################################################
{
    seal_chains;
    insert_jumps2cnt;
    insert_explicitjumps2cnt;
}

################################################################################
sub add_rules_from_file
################################################################################
{
    my ($file) = @_;
    my $table = 'undef';
    my $exit_code = open(RF,"<$file");
    if ( defined $exit_code ) {
        while (my $line = <RF>){
            if ($line =~ /^\*(filter|mangle|nat|raw)\s*$/) {
                $table = $1;
                next;
            }
            chomp($line);
            if ( $table ne 'undef' && $line ne '' ) {
                $line = eval("qq($line)"); # раскрываем значения переменных в строке
                update_filter_counters($1,1) if ($line =~ /^\s*\-[AI]\s+([_0-9A-z]+)(\s|$)/);
                gen($table,$line);
            }
        }
        close RF or return 1;
        return 0;
    } else { print "Can't open $file\n"; return 1; }
}

################################################################################
sub load_rules_from_file
################################################################################
{
    my ($file) = @_;
    my $exit_code = open(RF,"<$file");
    if ( defined $exit_code ) {
        my $ir_exit_code = open(IR, "| iptables-restore --noflush");
        if ( defined $ir_exit_code ) {
            while (my $line = <RF>){
                $line = eval("qq($line)"); # раскрываем значения переменных в строке
                chomp($line);
                print IR $line,"\n";
            }
            print IR "COMMIT\n";
            close IR or return 1;
        } else { print "Can't run 'iptables-restore'\n"; return 1; }
    } else { print "Can't open $file\n"; return 1; }
}

################################################################################
sub load_rules
################################################################################
{
    my $flush = defined $_[0] && $_[0] eq 'noflush' ? '--noflush' : '';
    my $out_file = $_[1];

    my $rule;
    my $ir_exit_code = open(IR, "| iptables-restore $flush");
    print "Loading rules via iptables-restore...\n";
    if ( defined $ir_exit_code ) {
        my $exit_code = open(OF,">$out_file") if defined $out_file;
        if (defined $out_file && ! defined $exit_code) {
            print "Warning: can't open $out_file\n";
        }
        print IR "*filter\n";
        print OF "*filter\n" if defined $out_file && defined $exit_code;
        foreach $rule (@filter_rules) { print IR $rule,"\n"; print OF $rule,"\n" if defined $out_file && defined $exit_code;}
        print IR "COMMIT\n";
        print OF "COMMIT\n" if defined $out_file && defined $exit_code;

        print IR "*mangle\n";
        print OF "*mangle\n" if defined $out_file && defined $exit_code;
        foreach $rule (@mangle_rules) { print IR $rule,"\n"; print OF $rule,"\n" if defined $out_file && defined $exit_code;}
        print IR "COMMIT\n";
        print OF "COMMIT\n" if defined $out_file && defined $exit_code;

        print IR "*nat\n";
        print OF "*nat\n" if defined $out_file && defined $exit_code;
        foreach $rule (@nat_rules) {print IR $rule,"\n"; print OF $rule,"\n" if defined $out_file && defined $exit_code;}
        print IR "COMMIT\n";
        print OF "COMMIT\n" if defined $out_file && defined $exit_code;

        print IR "*raw\n";
        print OF "*raw\n" if defined $out_file && defined $exit_code;
        foreach $rule (@raw_rules) { print IR $rule,"\n"; print OF $rule,"\n" if defined $out_file && defined $exit_code;}
        print IR "COMMIT\n";
        print OF "COMMIT\n" if defined $out_file && defined $exit_code;

        close OF if defined $out_file && defined $exit_code;
        if (! close IR) {print "\nRules loading error!\n"; return 1 } else {return 0}
    } else {print "Can't run 'iptables-restore'\n"; return 1}
}

################################################################################
sub load_tc_rules
################################################################################
{   my $out_file = $_[0];
    my $exit_code = open(OF,">$out_file") if defined $out_file;
    if (defined $out_file && ! defined $exit_code) {
        print "Warning: can't open $out_file\n";
    }
    foreach my $rule (@tc_rules) {
        print OF $rule,"\n" if defined $out_file && defined $exit_code;
        system($rule)
    }
    close OF if defined $out_file && defined $exit_code;
}
################################################################################
sub generate_save_counters
################################################################################
{

    system('cp -av '.$_[0].' '.$_[1]) == 0 || return 1;
    while (my ($chain, $v) = each %filter_count) {
        system("echo save_counters $v->{cnt_chain} ".lc($chain).' >> '.$_[1]);
    }
}

END { }
1;