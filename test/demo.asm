l2:
Pins (eth, 112)
Pins (vlan, 32)
Pins (qinq, 64)
Abegin
0x1, { (eth, 96, 16) == 0x8100,(vlan, 16, 16) == 0x800 }, 0x1, 0x3, 1
0x1, { (eth, 96, 16) == 0x88a8,(qinq, 16, 16) == 0x8100,(qinq, 48, 16) == 0x800 }, 0x2, 0x3, 1
0x1, { (eth, 96, 16) == 0x9200,(qinq, 16, 16) == 0x8100,(qinq, 48, 16) == 0x800 }, 0x3, 0x3, 1
0x1, { (eth, 96, 16) == 0x9300,(qinq, 16, 16) == 0x8100,(qinq, 48, 16) == 0x800 }, 0x4, 0x3, 1
0x1, { (eth, 96, 16) == 0x800 }, 0x5, 0x3, 1
Aend
ACbegin
0x1, { (mov (IRF,92,16), (vlan,0,16)),(set (IRF,16,8), 1), (set (IRF,24,8), 0) }, 0x12
0x2, { (mov (IRF,92,16), (vlan,0,16)),(mov (IRF,108,16), (vlan,0,16)),(set (IRF,16,8), 2), (set (IRF,24,8), 0) }, 0x16
0x3, { (set (IRF,16,8), 0), (set (IRF,24,8), 0) }, 0x16
0x4, { (set (IRF,16,8), 0), (set (IRF,24,8), 0) }, 0x16
0x5, { (set (IRF,32,8), 66) }, 0xe
ACend
B0begin
0x1, { (eth, 0, 48) == 0xffffffff }, 0x1
0x1, { (eth, 0, 48) == 0x1 }, 0x2
B0end
B0Cbegin
0x1, { (set (IRF,0,8), 3) }
0x2, { (set (IRF,0,8), 2) }
B0Cend
B1begin

B1end
B1Cbegin

B1Cend
l2s:

Abegin

Aend
ACbegin

ACend
B0begin

B0end
B0Cbegin

B0Cend
B1begin

B1end
B1Cbegin

B1Cend
l3:
Pins (v4, 160)
Abegin
0x3, { (ipv4, 4, 4) == 0x5,(ipv4, 72, 8) == 0x4 }, 0x1, 0x3, 0
0x3, { (ipv4, 4, 4) == 0x5,(ipv4, 72, 8) == 0x6 }, 0x2, 0x3, 1
0x3, { (ipv4, 4, 4) == 0x5,(ipv4, 72, 8) == 0x11 }, 0x3, 0x3, 1
0x3, { (ipv4, 4, 4) == 0x6,(ipv4, 72, 8) == 0x4 }, 0x4, 0x3, 0
0x3, { (ipv4, 4, 4) == 0x6,(ipv4, 72, 8) == 0x6 }, 0x5, 0x3, 1
0x3, { (ipv4, 4, 4) == 0x6,(ipv4, 72, 8) == 0x11 }, 0x6, 0x3, 1
0x3, { (ipv4, 4, 4) == 0x7,(ipv4, 72, 8) == 0x4 }, 0x7, 0x3, 0
0x3, { (ipv4, 4, 4) == 0x7,(ipv4, 72, 8) == 0x6 }, 0x8, 0x3, 1
0x3, { (ipv4, 4, 4) == 0x7,(ipv4, 72, 8) == 0x11 }, 0x9, 0x3, 1
Aend
ACbegin
0x1, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33)) }, 0x2
0x2, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 7), (set (IRF,16,2), 1) }, 0x2
0x3, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 0), (set (IRF,8,8), 1), (set (IRF,16,2), 2) }, 0x2
0x4, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33)) }, 0x3
0x5, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1) }, 0x3
0x6, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2) }, 0x3
0x7, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33)) }, 0x3
0x8, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1) }, 0x3
0x9, { (mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2) }, 0x3
ACend
B0begin
0x3, { (v4, 96, 32) == 0,(v4, 128, 32) == 0xffffffff }, 0x1
0x3, { (v4, 96, 32) == 0,(v4, 128, 32) == 0x7f }, 0x2
0x3, { (v4, 96, 32) == 0,(v4, 128, 32) == 0xe000000 }, 0x3
0x3, { (v4, 96, 32) == 0,(v4, 128, 32) == 0xe }, 0x4
0x3, { (v4, 96, 32) == 0x7f,(v4, 128, 32) == 0xffffffff }, 0x5
0x3, { (v4, 96, 32) == 0x7f,(v4, 128, 32) == 0x7f }, 0x6
0x3, { (v4, 96, 32) == 0x7f,(v4, 128, 32) == 0xe000000 }, 0x7
0x3, { (v4, 96, 32) == 0x7f,(v4, 128, 32) == 0xe }, 0x8
B0end
B0Cbegin
0x1, { (set (IRF,8,8),1),1 }
0x2, { (set (IRF,8,8),1),(set (IRF,0,8),1) }
0x3, { (set (IRF,8,8),1),(set (IRF,0,8),2) }
0x4, { (set (IRF,8,8),1),(set (IRF,0,8),4) }
0x5, { (set (IRF,16,8),1),(set (IRF,8,8),1) }
0x6, { (set (IRF,16,8),1),(set (IRF,0,8),1) }
0x7, { (set (IRF,16,8),1),(set (IRF,0,8),2) }
0x8, { (set (IRF,16,8),1),(set (IRF,0,8),4) }
B0Cend
B1begin
0x3, { (v4, 51, 13) == 0,(v4, 48, 3) == 0 }, 0x1
0x3, { (v4, 51, 13) == 0 }, 0x2
B1end
B1Cbegin
0x1, { (set (IRF,0,7),3) }
0x2, { (set (IRF,0,7),1) }
B1Cend
