l2:
Pins (eth, 112)
Pins (vlan, 32)
Pins (qinq, 64)
Abegin
0x1, {  }, 0x1, 0x3, 1
0x1, {  }, 0x2, 0x3, 1
0x1, {  }, 0x3, 0x3, 1
0x1, {  }, 0x4, 0x3, 1
0x1, {  }, 0x5, 0x3, 1
0x1, {  }, 0x6, 0x6, 2
Aend
l2s:

Abegin

Aend
l3:
Pins (v4, 160)
Abegin
0x3, { (ipv4, 4, 4) == 5,(ipv4, 72, 8) == 2 }, 0x1, 0x9, 2
0x3, { (ipv4, 4, 4) == 5,(ipv4, 72, 8) == 4 }, 0x2, 0x3, 0
0x3, { (ipv4, 4, 4) == 5,(ipv4, 72, 8) == 6 }, 0x3, 0xc, 1
0x3, { (ipv4, 4, 4) == 5,(ipv4, 72, 8) == 17 }, 0x4, 0xd, 1
0x3, { (ipv4, 4, 4) == 6,(ipv4, 72, 8) == 2 }, 0x5, 0x9, 2
0x3, { (ipv4, 4, 4) == 6,(ipv4, 72, 8) == 4 }, 0x6, 0x3, 0
0x3, { (ipv4, 4, 4) == 6,(ipv4, 72, 8) == 6 }, 0x7, 0xc, 1
0x3, { (ipv4, 4, 4) == 6,(ipv4, 72, 8) == 17 }, 0x8, 0xd, 1
0x3, { (ipv4, 4, 4) == 7,(ipv4, 72, 8) == 2 }, 0x9, 0x9, 2
0x3, { (ipv4, 4, 4) == 7,(ipv4, 72, 8) == 4 }, 0xa, 0x3, 0
0x3, { (ipv4, 4, 4) == 7,(ipv4, 72, 8) == 6 }, 0xb, 0xc, 1
0x3, { (ipv4, 4, 4) == 7,(ipv4, 72, 8) == 17 }, 0xc, 0xd, 1
Aend
