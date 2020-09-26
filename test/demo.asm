protocol ethernet = 112
protocol ieee802-1qTag = 32
protocol ieee802-1OuterTag = 64
protocol mpls = 32
protocol ipv4 = 160
l2:
Pins (eth, 112)
Pins (vlan, 32)
Pins (qinq, 64)
Abegin
0x1, 0x1
Aend
ACbegin
0x1
ACend
l2s:

Abegin
Aend
ACbegin
ACend
l3:
Pins (v4, 160)
Abegin
0x3, 0x1
0x3, 0x2
0x3, 0x3
Aend
ACbegin
0x1
0x2
0x3
ACend
