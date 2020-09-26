l2:

Pins (eth, 112)
Pins (vlan, 32)
Pins (qinq, 64)

Abegin  

0x1,{(eth, 96, 16) == 0x8100, (vlan, 16, 16) == 0x0800}, 0x1, 0x3, 1
0x1, {(eth, 96, 16) == 0x88a8, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1
0x1, {(eth, 96, 16) == 0x9200, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1
0x1, {(eth, 96, 16) == 0x9300, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1
0x1, {(eth, 96, 16) == 0x0800}, 0x3, 0x3, 1
// 0x1, {(eth, 96, 16) == 0x88cc}, 0x4, 0x6, 2

Aend

ACbegin

// 0x1,{(mov (IRF,92,16), (vlan,0,16)),(set (IRF,16,8), 1), (set (IRF,24,8), 0)}, 0x12
// 0x2,{(mov (IRF,92,16), (vlan,0,16)),(mov (IRF,108,16), (vlan,0,16)),(set (IRF,16,8), 2), (set (IRF,24,8), 0)}, 0x16
0x3,{(set (IRF,16,8), 0), (set (IRF,24,8), 0)}, 0xc
// 0x4,{(set (IRF,32,8), 66)}, 0xc

ACend

ANbegin

0x3, {( ) + (0 9)}, {( ) +(0xc 0xd 0xe 0xf 0x10 0x11 0x12 0x13}, {( ) + (6 7)}
0x6, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}

ANend

B0begin

0x1, {(eth, 0, 48) == 0xFFFFFFFFFFFF}, 0x1
0x1, {(eth, 40, 1) == 1}, 0x2

B0end

B0Cbegin

0x1, {(set (IRF,0,8), 3)}
0x2, {(set (IRF,0,8), 2)}

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

ANbegin

ANend

B0begin

B0end

B0Cbegin

B0Cend

B1begin

B1end

B1Cbegin

B1Cend

l3:

Pins (v4, 224)

Abegin  

// 0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 2}, 0x1, 0x9, 2
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 4}, 0x2, 0x3, 0
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 6}, 0x3, 0xc, 1
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 0x11}, 0x4, 0xd, 1
// 0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 2}, 0x5, 0x9, 2
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 4}, 0x6, 0x3, 0
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 6}, 0x7, 0xc, 1
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 0x11}, 0x8, 0xd, 1
// 0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 2}, 0x9, 0x9, 2
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 4}, 0xa, 0x3, 0
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 6}, 0xb, 0xc, 1
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 0x11}, 0xc, 0xd, 1

Aend

ACbegin

0x1,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x14
0x2,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 14
0x3, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 0), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x14
0x4,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 0), (set (IRF,8,8), 0), (set (IRF,16,2), 2)},14
0x5, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x18
0x6, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 0x18
0x7, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x18
0x8, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 0), (set (IRF,16,2), 2)}, 0x18
0x9, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x1c
0xa, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 0x1c
0xb, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x1c
0xc, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 0), (set (IRF,16,2), 2)}, 0x1c

ACend

ANbegin

0x9, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}
0x3, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}
0xc, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}
0xd, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}

ANend

B0begin

0x3, {(v4, 96, 32) == 0x00000000, (v4,128,32) == 0xffffffff}, 0x1//v4.srcAddr == 0x00000000  ,v4.dstAddr == 0xffffffff
0x3, {(v4, 96, 32) == 0x00000000, (v4,151,8) == 0x7f}, 0x2//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:24] == 0x7f
0x3, {(v4, 96, 32) == 0x00000000, (v4,136,24) == 0xe00000}, 0x3//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:8] == 0xe000000
0x3, {(v4, 96, 32) == 0x00000000, (v4,156,4) == 0xe}, 0x4//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:28] == 0xe
0x3, {(v4, 96, 32) == 0x00000000, ????????????????}, 0x5//v4.srcAddr == 0x00000000  ,dstAddr???????????????(graph?§Ö?else)
0x3, {(v4, 120, 8) == 0x7f, (v4,128,32) == 0xffffffff}, 0x6//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr == 0xffffffff
0x3, {(v4, 120, 8) == 0x7f, (v4, 151,8) == 0x7f}, 0x7//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:24] == 0x7f
0x3, {(v4, 120, 8) == 0x7f, (v4,136,24) == 0xe00000}, 0x8//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:8] == 0xe000000
0x3, {(v4, 120, 8) == 0x7f,(v4,156,4) == 0xe}, 0x9//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:28] == 0xe
0x3, {(v4, 120, 8) == 0x7f,dstAddr???????????????? }, 0xa//v4.srcAddr[31:24] == 0x7f ,dstAddr???????????????(graph?§Ö?else)
0x3, {v4.srcAddr????????????????,(v4,128,32) == 0xffffffff ?}, 0xb//v4.srcAddr???????????????,v4.dstAddr[31:28] == 0xffffffff
0x3, {v4.srcAddr????????????????,(v4, 151,8) == 0x7f}}, 0xc//v4.srcAddr???????????????,v4.dstAddr[31:24] == 0x7f
0x3, {v4.srcAddr????????????????,(v4,136,24) == 0xe00000}, 0xd//v4.srcAddr???????????????,v4.dstAddr[31:8] == 0xe000000
0x3, {v4.srcAddr????????????????,(v4,156,4) == 0xe}, 0xe//v4.srcAddr???????????????,v4.dstAddr[31:28] == 0xe

B0end

B0Cbegin

0x1, {(set (IRF,8,8),1),?}
0x2, {(set (IRF,8,8),1),(set (IRF,0,8),1)}
0x3, {(set (IRF,8,8),1),(set (IRF,0,8),2)}
0x4, {(set (IRF,8,8),1),(set (IRF,0,8),4)}
0x5, {(set (IRF,8,8),1)}
0x6, {(set (IRF,16,8),1),(set (IRF,8,8),1)}
0x7, {(set (IRF,16,8),1),(set (IRF,0,8),1)}
0x8, {(set (IRF,16,8),1),(set (IRF,0,8),2)}
0x9, {(set (IRF,16,8),1),(set (IRF,0,8),4)}
0xa, {(set (IRF,16,8),1)}
0xb, {(set (IRF,8,8),1)}
0xc, {(set (IRF,0,8),1)}
0xd, {(set (IRF,0,8),2)}
0xe, {(set (IRF,0,8),4)}

B0Cend

B1begin

0x3, {(v4, 51, 13) == 0, (v4,48,3) == 0}, 0x1
0x3, {(v4, 51, 13) == 0, (v4,48,3) == 0}, 0x2

B1end

B1Cbegin

0x1, {(set (IRF,0,7),3)}
0x2, {(set (IRF,0,7),1)}

B1Cend

l3s:

Abegin  

Aend

ACbegin

ACend

ANbegin

ANend

B0begin

B0end

B0Cbegin

B0Cend

B1begin

B1end

B1Cbegin

B1Cend
