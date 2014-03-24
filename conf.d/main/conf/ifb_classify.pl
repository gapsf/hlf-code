sub ifb_classify_prio0 {
    my ($p,$params) = @_;
    gen('mangle',"-A $p->{cn} -p tcp $p->{dstip} --tcp-flags SYN,ACK,FIN,RST ACK -m length --length 0:100 -j CLASSIFY --set-class $params->{class}");
    gen('mangle',"-A $p->{cn} -p udp $p->{dstip} --sport 53 -j CLASSIFY --set-class $params->{class}");
    gen('mangle',"-A $p->{cn} -p tcp $p->{dstip} -m multiport --sports 53,123,3389 -j CLASSIFY --set-class $params->{class}");
}

sub ifb_classify_prio1 {
    my ($p,$params) = @_;
    gen('mangle',"-A $p->{cn} -p tcp $p->{dstip} -m multiport --sports 80,123,443,3128,3129,1521 -j CLASSIFY --set-class $params->{class}");
    gen('mangle',"-A $p->{cn} -p tcp $p->{dstip} -m helper --helper ftp -j CLASSIFY --set-class $params->{class}");
}

sub ifb_classify_prio2 {
    my ($p,$params) = @_;
    gen('mangle',"-A $p->{cn} $p->{dstip} -j CLASSIFY --set-class $params->{class}");

}

sub subclasses {
    # на каждый вызов
    # генерируем три подчиненных класса для трафика с разным приоритетом и правила классификации
    use strict;
    my $p = $_[0];
    (my $n = $p->{dstip}) =~ s/[\.\-d\s]//g;
    $n = 'CLSFY_'.$n;
    my ($drate, $prefix ,$dunits) = ((my $down_rate = $p->{down_rate}) =~ /([0-9]+)([KM]*)([bit|bps]*)/i);
    $drate *= 1000 if $prefix eq 'K' || $prefix eq 'k';
    $drate *= 1000000 if $prefix eq 'M' || $prefix eq 'm';
    $drate *= 8 if lc($dunits) eq 'bps';
    my $subrate = int($drate/3);
    my @sub_handles = ();
    # 2,3,4 - приоритеты генерируемых классов
    for (2,3,4) {
        my $nh = sprintf("%x", $p->{tch}{$p->{qdiscid}}++);
        $sub_handles[$_] = $nh;
        gentc("tc class replace dev ifb0 parent $p->{classid} classid $p->{qdiscid}:$nh htb rate $subrate ceil $p->{down_ceil} prio $_ quantum 1540");
    }
    ifb_classify_prio2({cn => $n, dstip => ''},{class => $p->{qdiscid}.':'.$sub_handles[4]});
    ifb_classify_prio0({cn => $n, dstip => ''},{class => $p->{qdiscid}.':'.$sub_handles[2]});
    ifb_classify_prio1({cn => $n, dstip => ''},{class => $p->{qdiscid}.':'.$sub_handles[3]});
    gen('mangle',"-A $p->{cn} $p->{dstip} -j $n");
    $firewall::gv{'lan_host_rates'} += $drate;
}

