`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Alper Karadag, Ziya Erkoc
// Modified by: Hanzallah Azim Burney
// Create Date: 03.12.2018 19:22:49
//////////////////////////////////////////////////////////////////////////////////
module pipeline(input  clk,clear, execute_button, reset_button,     
                     output memwrite, output regwrite,  output DP, output [3:0] AN, output [6:0] C);
    logic clk_pulse, reset;
    logic [3:0] enables = 4'b1111;
    logic[31:0] writedata, dataadr, pc, instr;
    
    top  process(clk_pulse, reset, dataadr,  writedata, pc, instr, memwrite, regwrite); 
    
    display_controller disp(clk, reset,enables, writedata[7:4], writedata[3:0], dataadr[7:4], dataadr[3:0], AN, C, DP);  
    pulse_controller pulse1(clk, execute_button, clear,clk_pulse);
    pulse_controller pulse2(clk, reset_button, clear,reset);
endmodule

module top(input   logic 	 clk, reset,            
	     output  logic[31:0] dataadr, RD2D, PCF, instr,         
	     output  logic       memwrite, regwrite);
	     
	      logic [31:0] aluout, ResultW, ReadDataM, instrOut,WriteDataM;
	      logic[1:0] StallD, StallF;    
        
           // instantiate processor and memories  
           mips mipsMod(clk, reset, instr,ReadDataM, PCF, dataadr,ResultW, instrOut, WriteDataM, RD2D, StallD, StallF,
                         memwrite, regwrite); 
endmodule

module mips (input  logic        clk, reset,
            input  logic[31:0]  instr, ReadDataM, 
             output logic[31:0]  PCF,
             output logic[31:0]  aluout, resultW,
             output logic[31:0]  instrOut, WriteDataM, RD2D,
             output logic StallD, StallF, memwrite, regwrite);

    logic memtoreg, alusrc, regdst, jump, PCSrcM, branch;
    logic [31:0] PCPlus4F, PCBranchM, instrD;
    logic [2:0] alucontrol;
    assign instrOut = instr;
    
    logic [31:0]ALUOut;

    logic[31:0] PC;

    mux2 #(32) m1(PCPlus4F, PCBranchM, PCSrcM, PC);
    PipeWtoF wtf(PC, !StallF, clk, reset,PCF); 
    controller ctrl(instrD[31:26], instrD[5:0], memtoreg, memwrite, alusrc,regdst, regwrite, jump,alucontrol,
                       branch);
        
   datapath datapath(clk, reset, PCF, instr, regwrite, memtoreg, memwrite, alucontrol, alusrc, regdst, branch,
                    ReadDataM, PCSrcM, StallD, StallF,PCBranchM, PCPlus4F, instrD, ALUOut,
                    resultW, WriteDataM,RD2D, aluout); 
endmodule

// *******************************************************************************
// Below is the definition of the datapath.
// *******************************************************************************

module datapath (input  logic clk, reset,input logic [31:0] PCF, instr,input logic RegWriteD, MemtoRegD, MemWriteD,
		         input logic [2:0] ALUControlD,input logic AluSrcD, RegDstD, BranchD,input logic [31:0] ReadDataM,
		         output logic PCSrcM, StallD, StallF,output logic[31:0] PCBranchM, PCPlus4F, instrD, ALUOut, ResultW,WriteDataM,
		         output logic [31:0] RD2D, output logic [31:0]ALUOutM); 

    logic [31:0] SrcAE, SrcBE;
    logic [1:0] ForwardAE, ForwardBE;
        logic RegWriteW, MemtoRegW;

	logic ForwardAD, ForwardBD,  FlushE,FlushF, FlushD,RegWriteE, MemtoRegE, MemWriteE, AluSrcE, RegDstE, BranchE, Zero, RegWriteM, MemToRegM, MemWriteM, BranchM, ZeroM;		
	// Add necessary wires (logics).
	logic [4:0] RsD, RtD, RdD,RtE, RsE, RdE, WriteRegE, WriteRegM,WriteRegW;
    logic [31:0] ALUOutW, PCPlus4D, RD1D, SignImmD, RD1E, RD2E, SignImmE, PCPlus4E, WriteDataE, output1, PCBranchE, ReadData, ReadDataW;
    logic [2:0] AluControlE;
	
	assign PCSrcM = BranchM & ZeroM;
	assign RsD = instrD[25:21];
    assign RtD = instrD[20:16];
    assign RdD = instrD[15:11];

//    HazardUnit hu(RegWriteW, WriteRegW, RegWriteM, MemToRegM, WriteRegM, RegWriteE, MemtoRegE, RsE, RtE, RsD, RtD, PCSrcM, ForwardAE,
//                 ForwardBE, FlushE, StallD, StallF, FlushD,FlushF);
	
	HazardUnit hu(RegWriteW,PCSrcM, WriteRegW, RegWriteM, MemToRegM, WriteRegM,RegWriteE,MemtoRegE, RsE,RtE, RsD,RtD, 
                                ForwardAE,ForwardBE,FlushE,StallD,StallF);
     
     // added here
     imem imem(PCF[7:2], instr);  // added 
     dmem dmem(clk, MemWriteM, ALUOutM, WriteDataM, ReadDataM); // added 
                                
    adder pcadd(PCF, 32'd4, PCPlus4F); // changed to PCF
    PipeFtoD ftd(instr, PCPlus4F, !StallD, clk, (reset|FlushD), instrD, PCPlus4D); 
    signext se1(instrD[15:0], SignImmD);
    PipeDtoE dte(FlushE, clk, reset, RegWriteD, MemtoRegD, MemWriteD,ALUControlD,AluSrcD, RegDstD, BranchD,
                RD1D, RD2D, RsD, RtD, RdD,SignImmD, PCPlus4D,RegWriteE, MemtoRegE, MemWriteE, AluControlE,
                AluSrcE, RegDstE, BranchE,RD1E, RD2E, RsE, RtE, RdE, SignImmE,PCPlus4E);



    mux2 #(5) m3(RtE, RtD, RegDstE, WriteRegE);
    mux2 #(32) m4(WriteDataE, SignImmE, AluSrcE, SrcBE);
    mux4 #(32) m41(RD1E, ResultW, ALUOutM, 32'b0, ForwardAE, SrcAE);
    mux4 #(32) m42(RD2E, ResultW, ALUOutM, 32'b0, ForwardBE, WriteDataE);
    alu alu1(SrcAE, SrcBE, AluControlE, ALUOut, Zero, reset);
    logic[31:0] tempShift;
    sl2 shifter(SignImmE, tempShift);
    adder add1(PCPlus4E, tempShift, PCBranchE);
    
    PipeEtoM etm(clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,ALUOut,WriteDataE,WriteRegE,PCBranchE,
            RegWriteM, MemToRegM, MemWriteM, BranchM, ZeroM, ALUOutM, WriteDataM, WriteRegM, PCBranchM);
    
    
   
    PipeMtoW mtw(clk, reset, RegWriteM, MemToRegM,ReadDataM, ALUOutM, WriteRegM,
             RegWriteW, MemtoRegW, ReadDataW, ALUOutW, WriteRegW);

    mux2 #(32) m2( ALUOutW,ReadDataW, MemtoRegW, ResultW);
    regfile rf (clk, RegWriteW, instrD[25:21], instrD[20:16],
            WriteRegW, ResultW, RD1D, RD2D);                         
	
endmodule
    


// Define pipes that exist in the PipelinedDatapath. 
// The pipe between Writeback (W) and Fetch (F), as well as Fetch (F) and Decode (D) is given to you.
// Create the rest of the pipes where inputs follow the naming conventions in the book.


module PipeFtoD(input logic[31:0] instr, PcPlus4F,
                input logic EN, clk, reset,		// StallD will be connected as this EN
                output logic[31:0] instrD, PcPlus4D);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)begin
            instrD <= 0;
            PcPlus4D <= 0;
        end
        else if(EN)
            begin
            instrD<=instr;
            PcPlus4D<=PcPlus4F;
            end
        else begin
            instrD <= instrD;
            PcPlus4D <= PcPlus4D;
        end
    end
endmodule

// Similarly, the pipe between Writeback (W) and Fetch (F) is given as follows.

module PipeWtoF(input logic[31:0] PC,
                input logic EN, clk, reset,		// StallF will be connected as this EN
                output logic[31:0] PCF);
    
    always_ff @(posedge clk, posedge reset)begin
        if (reset)
            PCF <= 0;
        else if(EN)
            begin
            PCF<=PC;
            end
        else 
            PCF <= PCF;
    end
endmodule

// *******************************************************************************
// Below, you are given the argument lists of the modules PipeDtoE, PipeEtoM, PipeMtoW.
// You should implement them by looking at pipelined processor image given to you.   
// Don't forget that these codes are tested but you can always make changes if you want.
// Note that some output logics there for debugging purposes, in other words to trace their values in simulation.
// *******************************************************************************


module PipeDtoE(input logic clr, clk, reset, RegWriteD, MemtoRegD, MemWriteD,
                input logic[2:0] AluControlD,
                input logic AluSrcD, RegDstD, BranchD,
                input logic[31:0] RD1D, RD2D,
                input logic[4:0] RsD, RtD, RdD,
                input logic[31:0] SignImmD,
                input logic[31:0] PCPlus4D,
                    output logic RegWriteE, MemtoRegE, MemWriteE,
                    output logic[2:0] AluControlE,
                    output logic AluSrcE, RegDstE, BranchE,
                    output logic[31:0] RD1E, RD2E,
                    output logic[4:0] RsE, RtE, RdE,
                    output logic[31:0] SignImmE,
                    output logic[31:0] PCPlus4E);

    always_ff @(posedge clk, posedge reset)begin
        if (clr | reset)
            begin
                RegWriteE <= 1'b0;
                MemtoRegE <=  1'b0;
                MemWriteE <=  1'b0;
                AluControlE <=  3'b0;
                AluSrcE <=  1'b0;
                RegDstE <=  1'b0;
                BranchE <=  1'b0;
                RD1E <=  32'b0;
                RD2E <=  32'b0;
                RsE <=  5'b0;
                RtE <=  5'b0;
                RdE <=  5'b0;
                SignImmE <= 32'b0;
                PCPlus4E <= 32'b0;
            end
        else
            begin
                RegWriteE <= RegWriteD;
                MemtoRegE <= MemtoRegD;
                MemWriteE <= MemWriteD;
                AluControlE <= AluControlD;
                AluSrcE <= AluSrcD;
                RegDstE <= RegDstD;
                BranchE <= BranchD;
                RD1E <= RD1D;
                RD2E <= RD2D;
                RsE <= RsD;
                RtE <= RtD;
                RdE <= RdD;
                SignImmE <= SignImmD;
                PCPlus4E <= PCPlus4D;
            end
    end
endmodule

module PipeEtoM(input logic clk, reset, RegWriteE, MemtoRegE, MemWriteE, BranchE, Zero,
                input logic[31:0] ALUOut,
                input logic [31:0] WriteDataE,
                input logic[4:0] WriteRegE,
                input logic[31:0] PCBranchE,
                    output logic RegWriteM, MemtoRegM, MemWriteM, BranchM, ZeroM,
                    output logic[31:0] ALUOutM,
                    output logic [31:0] WriteDataM,
                    output logic[4:0] WriteRegM,
                    output logic[31:0] PCBranchM);
    
    always_ff @(posedge clk, posedge reset) begin
        if (reset)
            begin 
                RegWriteM <= 1'b0;
                MemtoRegM <= 1'b0;
                MemWriteM <= 1'b0;
                BranchM <= 1'b0;
                ZeroM <= 1'b0;
                ALUOutM <= 32'b0;
                WriteDataM <= 32'b0;
                WriteRegM <= 5'b0;
                PCBranchM <= 32'b0;
            end
        else
            begin 
                RegWriteM <= RegWriteE;
                MemtoRegM <= MemtoRegE;
                MemWriteM <= MemWriteE;
                BranchM <= BranchE;
                ZeroM <= Zero;
                ALUOutM <= ALUOut;
                WriteDataM <= WriteDataE;
                WriteRegM <= WriteRegE;
                PCBranchM <= PCBranchE;
            end
    end
endmodule

module PipeMtoW(input logic clk, reset, RegWriteM, MemtoRegM,
                input logic[31:0] ReadDataM, ALUOutM,
                input logic[4:0] WriteRegM,
                    output logic RegWriteW, MemtoRegW,
                    output logic[31:0] ReadDataW, ALUOutW,
                    output logic[4:0] WriteRegW);

		always_ff @(posedge clk, posedge reset) begin
            if (reset)
                begin
                    WriteRegW <= 5'b0;
                    RegWriteW <= 1'b0;
                    MemtoRegW <= 1'b0;
                    ReadDataW <= 32'b0;
                    ALUOutW <= 32'b0;
                end
            else
                begin
                    WriteRegW <= WriteRegM;
                    RegWriteW <= RegWriteM;
                    MemtoRegW <= MemtoRegM;
                    ReadDataW <= ReadDataM;
                    ALUOutW <= ALUOutM;
                end
        end
endmodule


module HazardUnit( input logic RegWriteW,
                input logic [4:0] WriteRegW, PCSrcM, 
                input logic RegWriteM,MemToRegM,
                input logic [4:0] WriteRegM,
                input logic RegWriteE,MemtoRegE,
                input logic [4:0] rsE,rtE,
                input logic [4:0] rsD,rtD,
                output logic [1:0] ForwardAE,ForwardBE,
                output logic FlushE,StallD,StallF);
   
    logic lwstall;
    assign lwstall = ((rsD == rtE) | (rtD == rtE)) & MemtoRegE;
    assign StallF = lwstall;
    assign StallD = lwstall;
    assign FlushE = lwstall | PCSrcM;
    
    always_comb begin
        

        if ((rsE != 0) & (rsE == WriteRegM) & RegWriteM)
            begin 
                ForwardAE = 10; 
            end
        else
            begin
                if ((rsE != 0) & (rsE == WriteRegW) & RegWriteW)
                    begin
                        ForwardAE = 01;
                    end
                else
                    begin
                        ForwardAE = 00;
                    end
            end

        if ((rtE != 0) & (rtE == WriteRegM) & RegWriteM)
            begin 
                ForwardBE = 10; 
            end
        else
            begin
                if ((rtE != 0) & (rtE == WriteRegW) & RegWriteW)
                    begin
                        ForwardBE = 01;
                    end
                else
                    begin
                        ForwardBE = 00;
                    end
            end
    end

endmodule

// External instruction memory used by MIPS single-cycle
// processor. It models instruction memory as a stored-program 
// ROM, with address as input, and instruction as output
// Modify it to test your own programs.

module imem ( input logic [5:0] addr, output logic [31:0] instr);

// imem is modeled as a lookup table, a stored-program byte-addressable ROM
	always_comb
	   case ({addr,2'b00})		   	// word-aligned fetch
//
// 	***************************************************************************
//	Here, you should paste the test cases that are given to you in lab document.
//  You can write your own test cases and try it as well.
//	Below is the program from the single-cycle lab.
//	***************************************************************************
//
//		address		instruction
//		-------		-----------
//		8'h00: instr = 32'h20080007;
//        8'h04: instr = 32'h20090005;
//        8'h08: instr = 32'h200a0000;
//        8'h0c: instr = 32'h210b000f;
//        8'h10: instr = 32'h01095020;
//        8'h14: instr = 32'h01095025;
//        8'h18: instr = 32'h01095024;
//        8'h1c: instr = 32'h01095022;
//        8'h20: instr = 32'h0109502a;
//        8'h24: instr = 32'had280002;
//        8'h28: instr = 32'h8d090000;
//        8'h2c: instr = 32'h1100fff5;
//        8'h30: instr = 32'h200a000a;
//        8'h34: instr = 32'h2009000c;
          8'h00: instr = 32'h20080005;
          8'h04: instr = 32'h21090006;
          8'h08: instr = 32'h01285020;

	     default:  instr = {32{1'bx}};	// unknown address
	   endcase
endmodule


// 	***************************************************************************
//	Below are the modules that you shouldn't need to modify at all..
//	***************************************************************************

module controller(input  logic[5:0] op, funct,
                  output logic     memtoreg, memwrite,
                  output logic     alusrc,
                  output logic     regdst, regwrite,
                  output logic     jump,
                  output logic[2:0] alucontrol,
                  output logic branch);

   logic [1:0] aluop;

   maindec md (op, memtoreg, memwrite, branch, alusrc, regdst, regwrite, 
         jump, aluop);

   aludec  ad (funct, aluop, alucontrol);

endmodule

// External data memory used by MIPS single-cycle processor

module dmem (input  logic        clk, we,
             input  logic[31:0]  a, wd,
             output logic[31:0]  rd);

   logic  [31:0] RAM[63:0];
  
   assign rd = RAM[a[31:2]];    // word-aligned  read (for lw)

   always_ff @(posedge clk)
     if (we)
       RAM[a[31:2]] <= wd;      // word-aligned write (for sw)

endmodule

module maindec (input logic[5:0] op, 
	              output logic memtoreg, memwrite, branch,
	              output logic alusrc, regdst, regwrite, jump,
	              output logic[1:0] aluop );
   logic [8:0] controls;

   assign {regwrite, regdst, alusrc, branch, memwrite,
                memtoreg,  aluop, jump} = controls;

  always_comb
    case(op)
      6'b000000: controls <= 9'b110000100; // R-type
      6'b100011: controls <= 9'b101001000; // LW
      6'b101011: controls <= 9'b001010000; // SW
      6'b000100: controls <= 9'b000100010; // BEQ
      6'b001000: controls <= 9'b101000000; // ADDI
      6'b000010: controls <= 9'b000000001; // J
      default:   controls <= 9'bxxxxxxxxx; // illegal op
    endcase
endmodule

module aludec (input    logic[5:0] funct,
               input    logic[1:0] aluop,
               output   logic[2:0] alucontrol);
  always_comb
    case(aluop)
      2'b00: alucontrol  = 3'b010;  // add  (for lw/sw/addi)
      2'b01: alucontrol  = 3'b110;  // sub   (for beq)
      default: case(funct)          // R-TYPE instructions
          6'b100000: alucontrol  = 3'b010; // ADD
          6'b100010: alucontrol  = 3'b110; // SUB
          6'b100100: alucontrol  = 3'b000; // AND
          6'b100101: alucontrol  = 3'b001; // OR
          6'b101010: alucontrol  = 3'b111; // SLT
          default:   alucontrol  = 3'bxxx; // ???
        endcase
    endcase
endmodule

module regfile (input    logic clk, we3, 
                input    logic[4:0]  ra1, ra2, wa3, 
                input    logic[31:0] wd3, 
                output   logic[31:0] rd1, rd2);

  logic [31:0] rf [31:0];

  // three ported register file: read two ports combinationally
  // write third port on rising edge of clock. Register0 hardwired to 0.

  always_ff @(negedge clk)
     if (we3) 
         rf [wa3] <= wd3;	

  assign rd1 = (ra1 != 0) ? rf [ra1] : 0;
  assign rd2 = (ra2 != 0) ? rf[ ra2] : 0;

endmodule

module alu(input  logic [31:0] a, b, 
           input  logic [2:0]  alucont, 
           output logic [31:0] result,
           output logic zero, input logic reset);

    always_comb begin
        case(alucont)
            3'b010: result = a + b;
            3'b110: result = a - b;
            3'b000: result = a & b;
            3'b001: result = a | b;
            3'b111: result = (a < b) ? 1 : 0;
            default: result = {32{1'bx}};
        endcase
        if(reset)
            result <= 0;
        end
    
    assign zero = (result == 0) ? 1'b1 : 1'b0;
    
endmodule

module adder (input  logic[31:0] a, b,
              output logic[31:0] y);
     
     assign y = a + b;
endmodule

module sl2 (input  logic[31:0] a,
            output logic[31:0] y);
     
     assign y = {a[29:0], 2'b00}; // shifts left by 2
endmodule

module signext (input  logic[15:0] a,
                output logic[31:0] y);
              
  assign y = {{16{a[15]}}, a};    // sign-extends 16-bit a
endmodule

// parameterized register
module flopr #(parameter WIDTH = 8)
              (input logic clk, reset, 
	       input logic[WIDTH-1:0] d, 
               output logic[WIDTH-1:0] q);

  always_ff@(posedge clk, posedge reset)
    if (reset) q <= 0; 
    else       q <= d;
endmodule


// paramaterized 2-to-1 MUX
module mux2 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1,  
              input  logic s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s ? d1 : d0; 
endmodule

// paramaterized 4-to-1 MUX
module mux4 #(parameter WIDTH = 8)
             (input  logic[WIDTH-1:0] d0, d1, d2, d3,  
              input  logic[1:0] s, 
              output logic[WIDTH-1:0] y);
  
   assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule

module display_controller (
		input logic clk, clear,
		input logic [3:0] enables, 
		input logic [3:0] digit3, digit2, digit1, digit0,
		output logic [3:0] AN,
		output logic [6:0] C,
		output logic       DP
		);

		logic [3:0] current_digit, cur_dig_AN;
		logic [6:0] segments;
		
      assign AN = ~(enables & cur_dig_AN);// AN signals are active low on the BASYS3 board,
                                // and must be enabled in order to display the digit
      assign C = ~segments;     // segments must be inverted, since the C values are active low
      assign DP = 1;            // makes the dot point always off 
                                // (0 = on, since it is active low)

// the 19-bit counter, runs at 100 MHz, so bit17 changes each 131072 clock cycles, 
//   or about once each 1.3 millisecond. Turning on and off the digits at this rate will
//   fool the human eye and make them appear to be on continuously
	   localparam N=19;
	   logic [N-1:0] count;
	always_ff @(posedge clk, posedge clear)
		if(clear) count <= 0;
		else count <= count + 1;	

// the upper 2 bits of count will cycle through the digits and the AN patterns
//  from left to right across the display unit			
	always_comb
	   case (count[N-1:N-2])
                // left most, AN3  
		2'b00: begin current_digit = digit3; cur_dig_AN = 4'b1000; end  
		2'b01: begin current_digit = digit2; cur_dig_AN = 4'b0100; end
		2'b10: begin current_digit = digit1; cur_dig_AN = 4'b0010; end
		2'b11: begin current_digit = digit0; cur_dig_AN = 4'b0001; end
                // right most, AN0
		default: begin current_digit = 4'bxxxx; cur_dig_AN = 4'bxxxx; end
	   endcase

// the hex-to-7-segment decoder
	always_comb
		case (current_digit)
		4'b0000: segments = 7'b111_1110;  // 0
		4'b0001: segments = 7'b011_0000;  // 1
		4'b0010: segments = 7'b110_1101;  // 2
		4'b0011: segments = 7'b111_1001;  // 3
		4'b0100: segments = 7'b011_0011;  // 4
		4'b0101: segments = 7'b101_1011;  // 5
		4'b0110: segments = 7'b101_1111;  // 6
		4'b0111: segments = 7'b111_0000;  // 7
		4'b1000: segments = 7'b111_1111;  // 8
		4'b1001: segments = 7'b111_0011;  // 9
		4'b1010: segments = 7'b111_0111;  // A
		4'b1011: segments = 7'b001_1111;  // b
		4'b1100: segments = 7'b000_1101;  // c
		4'b1101: segments = 7'b011_1101;  // d
		4'b1110: segments = 7'b100_1111;  // E
		4'b1111: segments = 7'b100_0111;  // F
		default: segments = 7'bxxx_xxxx;
		endcase		
endmodule


module pulse_controller(
	input CLK, sw_input, clear,
	output reg clk_pulse );

	 reg [2:0] state, nextstate;
	 reg [27:0] CNT; 
	 wire cnt_zero; 

	always @ (posedge CLK, posedge clear)
	   if(clear)
	    	state <=3'b000;
	   else
	    	state <= nextstate;

	always @ (sw_input, state, cnt_zero)
          case (state)
             3'b000: begin if (sw_input) nextstate = 3'b001; 
                           else nextstate = 3'b000; clk_pulse = 0; end	     
             3'b001: begin nextstate = 3'b010; clk_pulse = 1; end
             3'b010: begin if (cnt_zero) nextstate = 3'b011; 
                           else nextstate = 3'b010; clk_pulse = 1; end
             3'b011: begin if (sw_input) nextstate = 3'b011; 
                           else nextstate = 3'b100; clk_pulse = 0; end
             3'b100: begin if (cnt_zero) nextstate = 3'b000; 
                           else nextstate = 3'b100; clk_pulse = 0; end
            default: begin nextstate = 3'b000; clk_pulse = 0; end
          endcase

	always @(posedge CLK)
	   case(state)
		3'b001: CNT <= 100000000;
		3'b010: CNT <= CNT-1;
		3'b011: CNT <= 100000000;
		3'b100: CNT <= CNT-1;
	   endcase

//  reduction operator |CNT gives the OR of all bits in the CNT register	
	assign cnt_zero = ~|CNT;

endmodule