`timescale 1ns / 1ps
`include "CPU.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 
// Design Name: 
// Module Name: cpu_tb
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


module cpu_tb;

    reg clk, clrn;
    wire [31:0]pc;
    wire [31:0] inst;
    wire [31:0] aluout;
    wire [31:0] memout;
    
    CPU cpu(.clk(clk), .clrn(clrn), .pc(pc), .inst(inst), .aluout(aluout), .memout(memout));
    
    initial begin
        clk = 0;
        clrn = 1;
    end
    
    always #20 clk = !clk;
endmodule
