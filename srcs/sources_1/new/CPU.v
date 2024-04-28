`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 
// Design Name: 
// Module Name: CPU
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module CPU(clk, clrn, pc, inst, aluout, memout

    ); 
    
    input clk, clrn;
    wire [31:0] instr;
    wire [31:0] mux_pc;
    wire [31:0] jal_save;
    wire jal_e;
    wire [31:0] reg31;
    
    wire [31:0] r;
    
    reg [5:0] op;
    reg [5:0] func;
    
    wire [1:0] pcsrc;
    wire [3:0] aluc;
    wire shift;
    wire wreg;
    wire aluimm;
    wire wmem;
    wire m2reg;
    wire regrt;
    wire [4:0] wn;
    
    reg [4:0] rs;
    reg [4:0] rt;
    reg [4:0] rd;
    reg [4:0] sa;
    reg [15:0] imm;
    reg [25:0] jmpaddr;
    
    wire [31:0] imm_e;
    
    wire [31:0]qa;
    wire [31:0]qb;
    
    wire [31:0] a;
    wire [31:0] b;
    
    wire zero;
    
    wire [31:0] do;
    
    wire [31:0] mux_r;
    
    output reg [31:0]pc;
    output reg [31:0] inst;
    output reg [31:0] aluout;
    output reg [31:0] memout;
 
    
    always @(instr)
    begin
        op = instr[31:26];
        func = instr[5:0];
        rs = instr[25:21];
        rt = instr[20:16];
        rd = instr[15:11];
        sa = instr[10:6];
        imm = instr[15:0];
        jmpaddr = instr[25:0];
    end
    
    
    pc_select pcm(.clk(clk), .jal_e(jal_e), .jmpaddr(jmpaddr),.pcsrc(pcsrc), .imm_e(imm_e), .a(a), .mux_pc(mux_pc), .jal_save(jal_save));
    
    //jal_write jw(.clk(clk), .pcsrc(pcsrc), .wreg(wreg), .jal_save(jal_save), .wn(wn), .mux_r(mux_r));
    
    inst_mem im(.clk(clk),.pc(mux_pc), .instr(instr));
    
    control_unit cu(.op(op), .func(func), .pcsrc(pcsrc), .aluc(aluc), .shift(shift),.wreg(wreg), .
                     aluimm(aluimm), .wmem(wmem),.m2reg(m2reg),.regrt(regrt), .zero(zero), .jal_e(jal_e));
    
    mux_rf mrf(.rd(rd), .rt(rt),.regrt(regrt), .wn(wn));
    
    regfile rf(.rna(rs), .rnb(rt), .d(mux_r), .wn(wn), .we(wreg), .clk(clk), .clrn(clrn), .qa(qa), .qb(qb), 
                .reg31(reg31), .jal_e(jal_e), .jal_save(jal_save));
    
    mux_sa msa(.shift(shift), .sa(sa), .qa(qa), .qa2(a));
    
    mux_imm mimm(.aluimm(aluimm), .qb(qb), .imm_e(imm_e), .b(b));
    
    imm_extend imme(.imm(imm), .imm_e(imm_e));
    
    ALU alu(.a(a), .b(b), .aluc(aluc), .r(r), .zero(zero));
    
    //data_mem dm(.a(r), .di(qb), .we(wmem), .do(do));
    
    scdatamem scd(.clk(clk), .dataout(do), .datain(qb), .addr(r), .we(wmem));
    
    data_mux dmx(.r(r), .do(do), .m2reg(m2reg), .mux_r(mux_r));
    
    
    always @(*)
    begin
        pc = mux_pc;
        inst = instr;
        aluout = r;
        memout = do;
    end
   
    
endmodule


module control_unit(op, func, pcsrc, aluc, shift, wreg, aluimm, wmem, m2reg, regrt, zero, jal_e

    );
    input [5:0] op;
    input [5:0] func;
    input zero;
    
    output reg [1:0] pcsrc;
    output reg [3:0] aluc;
    output reg shift;
    output reg wreg;
    output reg aluimm;
    output reg wmem;
    output reg m2reg;
    output reg regrt;
    output reg jal_e;
    
    always @(*)
    begin
        case(op)
            6'b000000:
            begin
                aluimm = 0;
                wmem = 0;
                m2reg = 0;
                regrt = 0;
                jal_e = 0;
                case(func)
                    6'b100000: //R-add
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0000;
                            wreg = 1;
                            shift = 0;
                        end
                    6'b100010: //R-sub
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0001;
                            wreg = 1;
                            shift = 0;
                        end
                    6'b100100: //R-and
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0010;
                            wreg = 1;
                            shift = 0;
                        end
                    6'b100101: //R-or
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0011;
                            wreg = 1;
                            shift = 0;
                        end
                    6'b100110: //R-xor
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0100;
                            wreg = 1;
                            shift = 0;
                        end
                    6'b000000: //R-sll
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0101;
                            wreg = 1;
                            shift = 1;
                        end
                    6'b000010: //R-srl
                        begin
                            pcsrc = 2'b00;
                            aluc = 4'b0110;
                            wreg = 1;
                            shift = 1;
                        end
                    6'b001000: // jr
                        begin
                            pcsrc = 2'b10;
                            aluc = 4'b0000;
                            wreg = 0;
                            shift = 0;
                        end
                endcase
             end
                
           6'b001000: // I-addi
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0000;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 1;
                  jal_e = 0;
               end  
               
           6'b001100: // I-andi
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0010;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 1;
                  jal_e = 0;
               end  
          
          6'b001101: // I-ori
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0011;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 1;
                  jal_e = 0;
               end  
               
          6'b001110: // I-xori
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0100;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  wmem = 0;
                  m2reg = 0;
                  jal_e = 0;
                  regrt = 1;
               end  
               
         6'b001111: // I-lui
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0111;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  regrt = 1;
                  wmem = 0;
                  m2reg = 0;
                  jal_e = 0;
               end  
        6'b100011: // I-lw
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0000;
                  wreg = 1;
                  shift = 0;
                  aluimm = 1;
                  wmem = 0;
                  m2reg = 1;
                  regrt = 1;
                  jal_e = 0;
               end  
          6'b101011: // I-sw
               begin
                  pcsrc = 2'b00;
                  aluc = 4'b0000;
                  wreg = 0;
                  shift = 0;
                  aluimm = 1;
                  wmem = 1;
                  m2reg = 0;
                  regrt = 1;
                  jal_e = 0;
               end  
          6'b000100: //beq
                begin
                  if (zero)
                    pcsrc = 2'b01;
                  else
                    pcsrc = 2'b00;
                  aluc = 4'b0001;
                  wreg = 0;
                  shift = 0;
                  aluimm = 0;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 0;
                  jal_e = 0;
                end
           6'b000101: //bne
                begin
                  if (!zero)
                    pcsrc = 2'b01;
                  else
                    pcsrc = 2'b00;
                  aluc = 4'b0001;
                  wreg = 0;
                  shift = 0;
                  aluimm = 0;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 0;
                  jal_e = 0;
                end
             6'b000010: // j
                 begin
                  pcsrc = 2'b11;
                  aluc = 4'b0000;
                  wreg = 0;
                  shift = 0;
                  aluimm = 0;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 0;
                  jal_e = 0;
                end
             6'b000011: // jal
                begin
                  pcsrc = 2'b11;
                  aluc = 4'b0000;
                  wreg = 0;
                  shift = 0;
                  aluimm = 0;
                  wmem = 0;
                  m2reg = 0;
                  regrt = 0;
                  jal_e = 1;
                end
           
        endcase
    end
endmodule

module mux_imm(aluimm, qb, imm_e, b

    );
    input aluimm;
    input [31:0] qb;
    input [31:0] imm_e;
    
    output reg [31:0] b;
    
    
    always @(aluimm or qb or imm_e)
    begin
        if (aluimm)
            b = imm_e;
        else
            b = qb;
        
    end
endmodule

module imm_extend(imm, imm_e);
    input [15:0] imm;
    
    output reg[31:0] imm_e;
    
    always @(imm)
    begin
        imm_e = {{16{imm[15]}},imm[15:0]};
    end
endmodule


module ALU( a, b, aluc, r, zero
    );
    input [31:0] a;
    input [31:0] b;
    input [3:0] aluc;
    output reg [31:0] r;
    output reg zero;
    wire [31:0] extend;
   
    
    always@(a or b or aluc)
    begin
        case(aluc)
            4'b0000: // add
                begin
                    r = a + b;
                    zero = (r == 0)? 1:0;
                end
            4'b0001: //R-sub
                begin
                    r = a - b;
                    zero = (r == 0)? 1:0;
                end
            4'b0010: //R-and
                begin 
                    r = a & b;
                    zero = (r == 0)? 1:0;
                end
            4'b0011: //R-or
                begin
                    r = a | b;
                    zero = (r == 0)? 1:0;
                end
            4'b0100: //R-xor
                begin
                    r = a ^ b;
                    zero = (r == 0)? 1:0;
                end
            4'b0101: //R-sll
                begin
                    r = b << a;
                    zero = (r == 0)? 1:0;
                end
            4'b0110: //R-srl
                begin
                    r = b >> a;
                    zero = (r == 0)? 1:0;
                end
                
            4'b0111: //I-lui
                begin
                    r = b << 32'd16;
                end
          endcase
      end
    
endmodule

module regfile(rna, rnb, d, wn, we, clk, clrn, qa, qb, reg31, jal_e, jal_save);
    input [31:0] d;
    input [4:0] rna;
    input [4:0] rnb;
    input [4:0] wn;
    input we;
    input clk, clrn;
    input jal_e;
    input [31:0] jal_save;
    
    output [31:0] qa, qb;
    output [31:0] reg31;
    reg [31:0] register [1:31];
    
    
   
    
    assign qa = (rna == 0) ? 0 : register[rna]; //read port a
    assign qb = (rnb == 0) ? 0 : register[rnb]; //read port b
    assign reg31 = register[31];
    integer i;
   
    
    always @(posedge clk or negedge clrn)
        if (!clrn)
            for (i = 1; i < 32; i = i+1)
                register[i] <= 0;
        else if ((wn != 0) && we) 
  
                register[wn] <= d;
       else if (jal_e)
                register[31] = 32'h10;

            
              
    initial begin
    register[5'h0] = 32'h00000000;
    register[5'h1] = 32'ha00000aa;
    register[5'h2] = 32'h10000011;
    register[5'h3] = 32'h20000022;
    register[5'h4] = 32'h30000033;
    register[5'h5] = 32'h40000044;
    register[5'h6] = 32'h50000055;
    register[5'h7] = 32'h60000066;
    register[5'h8] = 32'h70000077;
    register[5'h9] = 32'h80000088;
    register[5'ha] = 32'h90000099;
    
    
   end
   
        
         
endmodule



module mux_sa(shift, sa, qa, qa2

    );
    input shift;
    input [4:0] sa;
    input [31:0] qa;
    
    output reg [31:0] qa2;
    reg [26:0] extend = 27'b0;
    
    always @(shift or sa or qa)
    begin
        if (shift)
            qa2 = {extend, sa};
        else
            qa2 = qa;
    end
endmodule

/*
module data_mem(a, di, we, do

    );
    input [31:0] a;   //addr by alu
    input [31:0] di; // dst or src
    input we;
    
    output reg [31:0] do;
    
    reg [31:0] RAM[0:255];
    reg [7:0] data_index;
    
    integer i;
    
    initial begin
        for (i = 0; i < 255; i = i+1)
            RAM[i] = 32'h0;
    end
    
    always @(a or we)
    begin
        data_index = a[7:0];
        if (we)     //sw
            RAM[data_index] <= di;
        else    //lw
            do <= RAM[data_index];
    end
    
endmodule
*/

module scdatamem (clk, dataout, datain, addr, we);
    input clk;
    input we;
    input [31:0] datain;
    input [31:0] addr;
    output [31:0] dataout;
    reg [31:0] ram [0:31];
    
    assign dataout = ram[addr[6:2]];
    always @(posedge clk)
        if (we) ram[addr[6:2]] = datain;
    
    integer i;
    initial begin
        for (i = 0; i < 32; i = i + 1)
            ram[i] = 0;
        ram[5'h14] = 32'h000000a3;
        ram[5'h15] = 32'h00000027; // (54hex)
        ram[5'h16] = 32'h00000079; // (58hex)
        ram[5'h17] = 32'h00000115;
    end
    
endmodule

module data_mux(r, do, m2reg, mux_r);
    input [31:0] r;
    input [31:0] do;
    input m2reg;
    
    output reg [31:0] mux_r;
    
    always @(*)
    begin
        if (m2reg ==1)      //lw
            mux_r = do;
        else
            mux_r = r;
    end
endmodule

module mux_rf(rd, rt,regrt, wn);
    input [4:0] rd;
    input [4:0] rt;
    input regrt;
    
    output reg [4:0] wn;
    
    always@(*)
    begin
        if (regrt)
            wn = rt;
        else
            wn = rd;
    end
    
endmodule




module pc_select (clk, jal_e, jmpaddr, pcsrc, imm_e, a, mux_pc, jal_save);
    input clk;
    input jal_e;
    input [25:0] jmpaddr;
    input [1:0] pcsrc;
    input [31:0] imm_e;
    input [31:0] a;
    reg [31:0] prev_pc;
    
    output reg[31:0] jal_save;
    output reg[31:0] mux_pc;
 
    initial begin
        prev_pc = 32'd0;
        mux_pc = 32'd0;
        //jal_save = 32'd4;
    end
    
    always @(posedge clk)
    begin
        
        case (pcsrc)
            2'b00:
            begin
           
                mux_pc = mux_pc + 32'd4;
                prev_pc = mux_pc;
          
            end
            
            2'b01:
            begin
                mux_pc = mux_pc + (imm_e << 32'd2) + 32'd4;
                prev_pc = mux_pc;
                
            end
            
            2'b10:
            begin
                mux_pc = a;
                prev_pc = mux_pc;
            end
            
            2'b11:
            begin
                mux_pc = {prev_pc[31:28], jmpaddr, 2'b00};
                if (jal_e)
                    jal_save = prev_pc + 32'd4;
            end
        endcase
           
    end
    
endmodule


module inst_mem(clk, pc, instr);
    input clk;
    input [31:0] pc;
    output reg [31:0] instr;
    
    reg [31:0] RAM [0:31];
    integer i;
    reg [4:0] counter; 
    
    always @(pc)
    begin
       
        counter = pc[6:2];
        instr = RAM[counter];
        
    end
    
    initial begin
        /*
        RAM[0] = 32'h3C010000; // main: 0: lui $1 0
        RAM[1] = 32'h34240080; // 04: ori $4 $1 80
        RAM[2] = 32'h20050004; // 08: addi $5 $0 4
        RAM[3] = 32'h00004020; // 0c: add $8 $0 $0
        RAM[4] = 32'hAC820000; // 10: sw $2 0($4)
        RAM[5] = 32'h8C890000; // 14: lw $9 0($4)
        RAM[6] = 32'h01244022; // 18: sub $8 $9 $4
        RAM[7] = 32'h20050003; // 1c: addi $5 $0 3
        RAM[8] = 32'h20A5FFFE; // loop2: 20: addi $5 $5 -1
        RAM[9] = 32'h34A8FFFF; // 24: ori $8, $5, 0xffff
        RAM[10] = 32'h39085555; // 28: xori $8, $8, 0x5555
        RAM[11] = 32'h2009FFFE; // 2c: addi $9, $0, -1
        RAM[12] = 32'h312AFFFF; // 30: andi $10, $9, 0xffff
        RAM[13] = 32'h01493025; // 34: or $6, $10, $9
        RAM[14] = 32'h01494026; // 38: xor $8, $10, $9
        RAM[15] = 32'h01463824; // 3c: and $7, $10, $6
        RAM[16] = 32'h10A00048; // 40: beq $5, $0, 0x48(shift)
        RAM[17] = 32'h08000020; // 44: j 20
        RAM[18] = 32'h2005FFFE; // 48: shift: addi $5, $0, -1
        
        
        RAM[0] = 32'h0C000002; // 0: jal 2
        RAM[1] = 32'h14A00002; // 4: bne $5, $0, 0x8(L1)
        RAM[2] = 32'h03E00008; // 8: jr $rs (rs = 31)
       */
        RAM[5'h0] = 32'h3c010000; // (00) main: lui $1, 0
        RAM[5'h1] = 32'h34240050; // (04) ori $4, $1, 80
        RAM[5'h2] = 32'h20050004; // (08) addi $5, $0, 4
        RAM[5'h3] = 32'h0c000018; // (0c) call: jal sum
        RAM[5'h4] = 32'hac820000; // (10) sw $2, 0($4)
        RAM[5'h5] = 32'h8c890000; // (14) lw $9, 0($4)
        RAM[5'h6] = 32'h01244022; // (18) sub $8, $9, $4
        RAM[5'h7] = 32'h20050003; // (1c) addi $5, $0, 3
        RAM[5'h8] = 32'h20a5ffff; // (20) loop2: addi $5, $5, -1
        RAM[5'h9] = 32'h34a8ffff; // (24) ori $8, $5, 0xffff
        RAM[5'ha] = 32'h39085555; // (28) xori $8, $8, 0x5555
        RAM[5'hb] = 32'h2009ffff; // (2c) addi $9, $0, -1
        RAM[5'hc] = 32'h312affff; // (30) andi $10,$9, 0xffff
        RAM[5'hd] = 32'h01493025; // (34) or $6, $10, $9
        RAM[5'he] = 32'h01494026; // (38) xor $8, $10, $9
        RAM[5'hf] = 32'h01463824; // (3c) and $7, $10, $6
        RAM[5'h10] = 32'h10a00001; // (40) beq $5, $0, shift
        RAM[5'h11] = 32'h08000008; // (44) j loop2
        RAM[5'h12] = 32'h2005ffff; // (48) shift: addi $5, $0, -1
        RAM[5'h13] = 32'h000543c0; // (4c) sll $8, $5, 15
        RAM[5'h14] = 32'h00084400; // (50) sll $8, $8, 16
        RAM[5'h15] = 32'h00084403; // (54) sra $8, $8, 16
        RAM[5'h16] = 32'h000843c2; // (58) srl $8, $8, 15
        RAM[5'h17] = 32'h08000017; // (5c) finish: j finish
        RAM[5'h18] = 32'h00004020; // (60) sum: add $8, $0, $0
        RAM[5'h19] = 32'h8c890000; // (64) loop: lw $9, 0($4)
        RAM[5'h1a] = 32'h20840004; // (68) addi $4, $4, 4
        RAM[5'h1b] = 32'h01094020; // (6c) add $8, $8, $9
        RAM[5'h1c] = 32'h20a5ffff; // (70) addi $5, $5, -1
        RAM[5'h1d] = 32'h14a0fffb; // (74) bne $5, $0, loop
        RAM[5'h1e] = 32'h00081000; // (78) sll $2, $8, 0
        RAM[5'h1f] = 32'h03e00008; // (7c) jr $31
        
    end
    
    
endmodule

