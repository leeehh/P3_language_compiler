//#############################################################################################################################################################################
//协议帧报头格式：
//L2header
//Ethernet II:DMAC(6B)+SMAC(6B)+Type(2B)
//VLAN(18B)  :DMAC(6B)+SMAC(6B)+Type(2B)+TAG(2B:PRI/3b+CFI/1b+VID/12b)+Length/Type(2B)
//QinQ(22B)  :DMAC(6B)+SMAC(6B)+EType(2B)+TAG(2B:Pri/3b+CFI/1b+VID/12b)+EType(2B)+TAG(2B:Pri/3b+CFI/1b+VID/12b)+LEN/ETYPE(2B)

//MPLS(one)  :Label(20bit)+EXP(3bit)+S(1bit)+TTL(8bit)

//L3header(IPheader)
//IPv4(20B)  :Ver(4bit)+IHL(4bit)+TyoS(8bit)+TtlLen(16bit)+Iden(16bit)+Flg(3bit)+FraOffset(13bit)+TimeTOLive(8bit)+Protocol(8bit)+HdrCheSUM(16bit)+SAddr(32bit)+DAddr(32bit)
//IPv6(40B)  :Ver(4bit)+TraClass(8bit)+FlowLab(20bit)+PayloadLen(16bit)+NxtHeader(8bit)+HopLimit(8bit)+SAddr(128bit)+DAddr(128bit)

//L4header
//TCP (20B)  :SPort(16bit)+DPort(16bit)+SequNum(32bit)+AcknNum(32bit)+DataOffset(4bit)+Reserved(6bit)+URG(1bit)+ACK(1bit)+PSH(1bit)+RST(1bit)+SYN(1bit)+FIN(1bit)+Win(16bit)+CheckSUM(16bit)+UrgPoin(16bit)
//UDP ( 8B)  :SPort(2B)+DPort(2B)+Length(2B)+CheckSUM(2B)

//#############################################################################################################################################################################
//配置文件包头格式(MPLS L3VPN)：
//L2header(6B+6B+n*4B+2B)+MPLS(n*4B)  +L3header(20B)+L4header
//QinQ(22B)              +One MPLS(4B)+IPv4(20B)    +UDP(8B)

//#############################################################################################################################################################################
l2:

Pins (eth, 112)   // size: 8*14
Pins (vlan, 32)   // size: 8*4
Pins (qinq, 64)   // size: 8*8

Abegin  

//cella_pb(407bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)+nxt_id(7)+bypass(2:mainbypass(1)+subbypass(1))

0x1,{(eth, 96, 16) == 0x8100, (vlan, 16, 16) == 0x0800}, 0x1, 0x3, 1//eth+vlan+ipv4
0x1, {(eth, 96, 16) == 0x88a8, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1//eth+qinq+ipv4
0x1, {(eth, 96, 16) == 0x9200, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1//eth+qinq+ipv4
0x1, {(eth, 96, 16) == 0x9300, (qinq, 16, 16) == 0x8100, (qinq, 48, 16) ==  0x0800},0x2,0x3,1//eth+qinq+ipv4
0x1, {(eth, 96, 16) == 0x0800}, 0x3, 0x3, 1//eth+ipv4
0x1, {(eth, 96, 16) == 0x88cc}, 0x4, 0x6, 2//eth+lldp
//

Aend

**************************************************************************************************************************************************************************//

ACbegin

//cella_pc_cur(328bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))+lyr_offset(8)
0x1,{(mov (IRF,192,16), (vlan,0,16)),(set (IRF,16,8), 1), (set (IRF,24,8), 0)}, 0x12//sub_id:01,mov {IRF_outer_vlan_high, IRF_outer_vlan_low}, {vlan.pcp,vlan.cfi,vlan.vid};set IRF_tag_type_2b, 1;set IRF_pkt_type_3b, 0;
0x2,{(mov (IRF,192,16), (vlan,0,16)),(mov (IRF,208,16), (vlan,0,16)),(set (IRF,16,8), 2), (set (IRF,24,8), 0)}, 0x16//sub_id:02,mov {IRF_outer_vlan_high, IRF_outer_vlan_low}, {qinq.pcp_o,qinq.cfi_o,qinq.vid_o};mov {IRF_inner_vlan_high, IRF_inner_vlan_low}, {qinq.pcp_i,qinq.cfi_i,qinq.vid_i};set IRF_tag_type_2b, 2;set IRF_pkt_type_3b, 0;
0x3,{(set (IRF,16,8), 0), (set (IRF,24,8), 0)}, 0xc//sub_id:03,set IRF_tag_type_2b, 0;set IRF_pkt_type_3b, 0;
0x4,{(set (IRF,32,8), 66)}, 0xc//sub_id:04,set IRF_l2_protocol_flag_type_8b, 66;
//

ACend

**************************************************************************************************************************************************************************//

ANbegin

//cella_pc_nxt(583bit*32)
//nxt_id(7)+pa_offset(3*24*8b:cellA(irf/2+fra/22)+cellB0(irf/2+fra/22)+cellB1(irf/2+fra/22))

0x3, {( ) + (0 9)}, {( ) +(0xc 0xd 0xe 0xf 0x10 0x11 0x12 0x13}, {( ) + (6 7)}//ipv4
0x6, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}//lldp
//

ANend

**************************************************************************************************************************************************************************//

B0begin

//cellb0_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)

0x1, {(eth, 0, 48) == 0xFFFFFFFFFFFF}, 0x1//eth.dmac == 0xFFFFFFFFFFFF
0x1, {(eth, 40, 1) == 1}, 0x2//eth.dmac[40] == 1

B0end

//**************************************************************************************************************************************************************************//

B0Cbegin

//cellb0_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))
0x2, {(set (IRF,0,8), 3)}//sub_id:01,set IRF_l2_type = 3;
0x2, {(set (IRF,0,8), 2)}//sub_id:02,set IRF_l2_type = 2;
//

B0Cend

**************************************************************************************************************************************************************************//

B1begin

//cellb1_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)


B1end

//**************************************************************************************************************************************************************************//

B1Cbegin

//cellb1_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B1Cend//

############################################################################################################################################################################
l2s:

Abegin  

//cella_pb(407bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)+nxt_id(7)+bypass(2:mainbypass(1)+subbypass(1))


Aend

**************************************************************************************************************************************************************************//

ACbegin

//cella_pc_cur(328bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))+lyr_offset(8)

//

ACend

**************************************************************************************************************************************************************************//

ANbegin

//cella_pc_nxt(583bit*32)
//nxt_id(7)+pa_offset(3*24*8b)

ANend

//**************************************************************************************************************************************************************************//

B0begin

//cellb0_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)

B0end

//**************************************************************************************************************************************************************************//

B0Cbegin
 
//cellb0_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B0Cend

//**************************************************************************************************************************************************************************//

B1begin

//cellb1_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)


B1end

//**************************************************************************************************************************************************************************//

B1Cbegin

//cellb1_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B1Cend//

//#############################################################################################################################################################################
l3:

Pins (v4, 224)   // size: 8*28

Abegin  

//cella_pb(407bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)+nxt_id(7)+bypass(2:mainbypass(1)+subbypass(1))

0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 2}, 0x1, 0x9, 2//ihl == 5,theProtocol == 2
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 4}, 0x2, 0x3, 0//ihl == 5,theProtocol == 4
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 6}, 0x3, 0xc, 1//ihl == 5,theProtocol == 6
0x3, {(v4, 4, 4) == 5, (v4, 72, 8) == 0x11}, 0x4, 0xd, 1//ihl == 5,theProtocol == 0x11
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 2}, 0x5, 0x9, 2//ihl == 6,theProtocol == 2
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 4}, 0x6, 0x3, 0//ihl == 6,theProtocol == 4
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 6}, 0x7, 0xc, 1//ihl == 6,theProtocol == 6
0x3, {(v4, 4, 4) == 6, (v4, 72, 8) == 0x11}, 0x8, 0xd, 1//ihl == 6,theProtocol == 0x11
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 2}, 0x9, 0x9, 2//ihl == 7,theProtocol == 2
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 4}, 0xa, 0x3, 0//ihl == 7,theProtocol == 4
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 6}, 0xb, 0xc, 1//ihl == 7,theProtocol == 6
0x3, {(v4, 4, 4) == 7, (v4, 72, 8) == 0x11}, 0xc, 0xd, 1//ihl == 7,theProtocol == 0x11

//

Aend

**************************************************************************************************************************************************************************//

ACbegin

//cella_pc_cur(328bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))+lyr_offset(8)
0x1,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x14//sub_id:01,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 0;set IRF_l3_encode, 3;set IRF_l3_type[1:0], 0;set IRF_l3_protocol_flag_type_8b, 33;
0x2,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 0), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 14//sub_id:02,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 0;set IRF_l3_encode, 7;set IRF_l3_type[1:0], 1;
0x3, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 0), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x14//sub_id:03,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 0;set IRF_l3_encode, 1;set IRF_l3_type[1:0], 2;
0x4,{(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 0), (set (IRF,8,8), 0), (set (IRF,16,2), 2)},14//sub_id:04,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 0;set IRF_l3_encode, 0;set IRF_l3_type[1:0], 2;
0x5, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x18//sub_id:05,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 3;set IRF_l3_type[1:0], 0;set IRF_l3_protocol_flag_type_8b, 33;
0x6, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 0x18//sub_id:06,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 7;set IRF_l3_type[1:0], 1;
0x7, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x18//sub_id:07,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 1;set IRF_l3_type[1:0], 2;
0x8, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 0), (set (IRF,16,2), 2)}, 0x18//sub_id:08,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 0;set IRF_l3_type[1:0], 2;
0x9, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 3),(set (IRF,16,2),0), (set (IRF,24,8), 33))}, 0x1c//sub_id:09,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 3;set IRF_l3_type[1:0], 0;set IRF_l3_protocol_flag_type_8b, 33;
0xa, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)), (set (IRF,19,1), 1), (set (IRF,8,8), 7), (set (IRF,16,2), 1)}, 0x1c//sub_id:0a,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 7;set IRF_l3_type[1:0], 1;
0xb, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 1), (set (IRF,16,2), 2)}, 0x1c//sub_id:0b,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 1;set IRF_l3_type[1:0], 2;
0xc, {(mov (IRF,192,8), (v4,8,8)),(mov (IRF,200,8), (v4,64,8)), (lg  (IRF,384,8), 2, (v4,64,8)),  (set (IRF,19,1), 1), (set (IRF,8,8), 0), (set (IRF,16,2), 2)}, 0x1c//sub_id:0c,mov IRF_TOS_8b, v4.diffserv;mov IRF_ttl_8b, v4.ttl;lg IRF_TTL_EXP, 2, v4.ttl;set IRF_l3_type[3], 1;set IRF_l3_encode, 0;set IRF_l3_type[1:0], 2;

//

ACend

**************************************************************************************************************************************************************************//

ANbegin

//cella_pc_nxt(583bit*32)
//nxt_id(7)+pa_offset(3*24*8b)

0x9, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}//igmp
0x3, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}//ipv4
0xc, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}//tcp
0xd, {( ) + ( )}, {( ) + ( )}, {( ) + ( )}//udp
//修改后，当前应该为空，因为没有给后续报文格式

ANend

//**************************************************************************************************************************************************************************//

B0begin

//cellb0_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)

0x3, {(v4, 96, 32) == 0x00000000, (v4,128,32) == 0xffffffff}, 0x1//v4.srcAddr == 0x00000000  ,v4.dstAddr == 0xffffffff
0x3, {(v4, 96, 32) == 0x00000000, (v4,151,8) == 0x7f}, 0x2//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:24] == 0x7f
0x3, {(v4, 96, 32) == 0x00000000, (v4,136,24) == 0xe00000}, 0x3//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:8] == 0xe000000
0x3, {(v4, 96, 32) == 0x00000000, (v4,156,4) == 0xe}, 0x4//v4.srcAddr == 0x00000000  ,v4.dstAddr[31:28] == 0xe
0x3, {(v4, 96, 32) == 0x00000000, 上述四种都不满足?}, 0x5//v4.srcAddr == 0x00000000  ,dstAddr上述四种都不满足(graph中的else)
0x3, {(v4, 120, 8) == 0x7f, (v4,128,32) == 0xffffffff}, 0x6//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr == 0xffffffff
0x3, {(v4, 120, 8) == 0x7f, (v4, 151,8) == 0x7f}, 0x7//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:24] == 0x7f
0x3, {(v4, 120, 8) == 0x7f, (v4,136,24) == 0xe00000}, 0x8//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:8] == 0xe000000
0x3, {(v4, 120, 8) == 0x7f,(v4,156,4) == 0xe}, 0x9//v4.srcAddr[31:24] == 0x7f ,v4.dstAddr[31:28] == 0xe
0x3, {(v4, 120, 8) == 0x7f,dstAddr上述四种都不满足? }, 0xa//v4.srcAddr[31:24] == 0x7f ,dstAddr上述四种都不满足(graph中的else)
0x3, {v4.srcAddr上面两种都不满足?,(v4,128,32) == 0xffffffff ?}, 0xb//v4.srcAddr上面两种都不满足,v4.dstAddr[31:28] == 0xffffffff
0x3, {v4.srcAddr上面两种都不满足?,(v4, 151,8) == 0x7f}}, 0xc//v4.srcAddr上面两种都不满足,v4.dstAddr[31:24] == 0x7f
0x3, {v4.srcAddr上面两种都不满足?,(v4,136,24) == 0xe00000}, 0xd//v4.srcAddr上面两种都不满足,v4.dstAddr[31:8] == 0xe000000
0x3, {v4.srcAddr上面两种都不满足?,(v4,156,4) == 0xe}, 0xe//v4.srcAddr上面两种都不满足,v4.dstAddr[31:28] == 0xe

B0end

//**************************************************************************************************************************************************************************//

B0Cbegin

//cellb0_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))
0x1, {(set (IRF,8,8),1),?}//sub_id:01,set IRF_IPV4_IP_SPECIAL, 1;set IRF_IPV4_IP_SPECIAL, 1;
0x2, {(set (IRF,8,8),1),(set (IRF,0,8),1)}//sub_id:02,set IRF_IPV4_IP_SPECIAL, 1;set IRF_DIP_LB_MUL, 1;
0x3, {(set (IRF,8,8),1),(set (IRF,0,8),2)}//sub_id:03,set IRF_IPV4_IP_SPECIAL, 1;set IRF_DIP_LB_MUL, 2;
0x4, {(set (IRF,8,8),1),(set (IRF,0,8),4)}//sub_id:04,set IRF_IPV4_IP_SPECIAL, 1;set IRF_DIP_LB_MUL, 4;	
0x5, {(set (IRF,8,8),1)}//sub_id:05,set IRF_IPV4_IP_SPECIAL, 1;
0x6, {(set (IRF,16,8),1),(set (IRF,8,8),1)}//sub_id:06,set IRF_IPV4_SIP_LB, 1;set IRF_IPV4_IP_SPECIAL, 1;
0x7, {(set (IRF,16,8),1),(set (IRF,0,8),1)}//sub_id:07,set IRF_IPV4_SIP_LB, 1;set IRF_DIP_LB_MUL, 1;
0x8, {(set (IRF,16,8),1),(set (IRF,0,8),2)}//sub_id:08,set IRF_IPV4_SIP_LB, 1;set IRF_DIP_LB_MUL, 2;
0x9, {(set (IRF,16,8),1),(set (IRF,0,8),4)}//sub_id:09,set IRF_IPV4_SIP_LB, 1;set IRF_DIP_LB_MUL, 4;
0xa, {(set (IRF,16,8),1)}//sub_id:0a,set IRF_IPV4_SIP_LB, 1;
0xb, {(set (IRF,8,8),1)}//sub_id:0b,set IRF_IPV4_IP_SPECIAL, 1;
0xc, {(set (IRF,0,8),1)}//sub_id:0c,set IRF_DIP_LB_MUL, 1;
0xd, {(set (IRF,0,8),2)}//sub_id:0d,set IRF_DIP_LB_MUL, 2;
0xe, {(set (IRF,0,8),4)}//sub_id:0e,set IRF_DIP_LB_MUL, 4;

//

B0Cend

**************************************************************************************************************************************************************************//

B1begin

//cellb1_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)

0x3, {(v4, 51, 13) == 0, (v4,48,3) == 0}, 0x1//v4.flagOffset == 0,v4.flags == 0
0x3, {(v4, 51, 13) == 0, (v4,48,3) =\= 0 ?}, 0x2//v4.flagOffset == 0,v4.flags != 0

B1end

//**************************************************************************************************************************************************************************//

B1Cbegin

//cellb1_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))
0x1, {(set (IRF,0,7),3)} //sub_id:01,set IRF_IP_FRAG_STATUS, 3;
0x2, {(set (IRF,0,7),1)} //sub_id:02,set IRF_IP_FRAG_STATUS, 1;

B1Cend//

//#############################################################################################################################################################################
l3s:

Abegin  

//cella_pb(407bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)+nxt_id(7)+bypass(2:mainbypass(1)+subbypass(1))


Aend

//**************************************************************************************************************************************************************************//

ACbegin

//cella_pc_cur(328bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))+lyr_offset(8)

//

ACend

**************************************************************************************************************************************************************************//

ANbegin

//cella_pc_nxt(583bit*32)
//nxt_id(7)+pa_offset(3*24*8b)


ANend

//**************************************************************************************************************************************************************************//

B0begin

//cellb0_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)


B0end

//**************************************************************************************************************************************************************************//

B0Cbegin

//cellb0_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B0Cend

//**************************************************************************************************************************************************************************//

B1begin

//cellb1_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)


B1end

//**************************************************************************************************************************************************************************//

B1Cbegin

//cellb1_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B1Cend//

//#############################################################################################################################################################################
l4:

Abegin  

//cella_pb(407bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)+nxt_id(7)+bypass(2:mainbypass(1)+subbypass(1))


Aend

//
**************************************************************************************************************************************************************************//

ACbegin

//cella_pc_cur(328bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))+lyr_offset(8)

//

ACend

*************************************************************************************** ***********************************************************************************//

ANbegin

//cella_pc_nxt(583bit*32)
//nxt_id(7)+pa_offset(3*24*8b)


ANend

//**************************************************************************************************************************************************************************//

B0begin

//cellb0_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)


B0end

//**************************************************************************************************************************************************************************//

B0Cbegin

//cellb0_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B0Cend

//**************************************************************************************************************************************************************************//

B1begin

//cellb1_pb(398bit*32)
//hdr_id(7)+mask(24*8b)+value(24*8b)+sub_id(7)

B1end

//**************************************************************************************************************************************************************************//

B1Cbegin

//cellb1_pc_cur(320bit*32)
//vliw(320:alu(8*24b)+mov(8*8b)+set(8*8b))

B1Cend//

//#############################################################################################################################################################################