//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


// Bind statement usage in mixed-langage environments
//			https://www.youtube.com/watch?v=VuBqJoTRYyU


bind Registers RegisterBankCoverage u_RegisterBankCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_writeEnable(writeEnable),
	.cov_writeAck(writeAck),
	.cov_readEnable(readEnable),
	.cov_address(address)
	);

module RegisterBankCoverage
	//#(parameter g_ChannelId = 15)
	(
	input logic cov_reset,
	input logic cov_clk,
    input logic cov_writeEnable,
    input logic cov_readEnable,
    input logic cov_writeAck,
    input logic [7:0] cov_address
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

// Check that read strobes only 1 clock
property p_read_strobe_once;
	$rose(cov_readEnable) |=> $fell(cov_readEnable);
endproperty
ast_read_strobe_once : assert property(p_read_strobe_once);
cov_read_strobe_once : cover property(p_read_strobe_once);

// Check that write strobes only 1 clock
property p_write_ack_twice;
	$rose(cov_writeAck) |=> cov_writeAck ##1 $fell(cov_writeAck);
endproperty
ast_write_ack_twice : assert property(p_write_ack_twice);
cov_write_ack_twice : cover property(p_write_ack_twice);

// cover group: log if read and write access occured for all
// documented register address
// Lab: this covergroup will not work properly. Explore why and update.
covergroup covg_RegisterAccess
    @(negedge cov_clk && (cov_readEnable || cov_writeEnable) iff !cov_reset) ;
	option.name		= "cov_RegisterAccess";
    readMode       : coverpoint cov_readEnable {
        bins b = {1};
    }
    writeMode     : coverpoint cov_writeEnable {
        bins b = {1};
    }
    addressSpace  : coverpoint cov_address {
        bins b [] = {0,1,2,3,4,5,6,7,8,9};
    }
endgroup

covg_RegisterAccess cov_userifCover = new();



// TESTS SVA

// TODO
// Reset - Au prochain coup de clk, writeAck devient 0 et readData devient 0
property reset_writeack_readdata;
    // readData PAS DANS LES SIGNAUX DE CE FICHIER
    @(posedge cov_clk) $rose(cov_reset) |=> cov_writeAck == 0;
endproperty
reset_writeack_readdata_check: assert property(reset_writeack_readdata) 
  else $display($stime,,,"\t\tRESET WRITEACK AND READDATA FAIL:: WriteAck and readData weren't zeroed at reset \n");

// writeEnable reste 1 tant que writeACK reste 0
property writeEnable_one_writeACK_zero;
    @(posedge cov_clk) cov_writeEnable == 1 |-> $past(cov_writeAck,1) == 0;
endproperty
writeEnable_one_writeACK_zero_check: assert property(writeEnable_one_writeACK_zero) 
  else $display($stime,,,"\t\tWRITEENABLE WRITEACK FAIL:: The value of writeEnable changed to not(1) while writeAck was stable at 0\n");

// changement de readData 1 clk après readEnable
/*
property readData_after_readEnable;
    @(posedge cov_clk) cov_readEnable == 1 |=> ##1 !$stable(cov_readData);
endproperty
readData_after_readEnable_check: assert property(readData_after_readEnable) 
  else $display($stime,,,"\t\tWRITEENABLE WRITEACK FAIL:: The value of writeEnable changed to not(1) while writeAck was stable at 0\n");
*/

// AUTRE

// Vérifier la présence de writeData et address

// writeACK devient 1 pour 2 clk
property writeEnable_one_writeACK_2clk;
    @(posedge cov_clk) $rose(cov_writeAck) && cov_writeEnable == 1 |->  ##[1:2] cov_writeAck == 1;
endproperty
cover_writeEnable_one_writeACK_2clk: cover property(writeEnable_one_writeACK_2clk);
writeEnable_one_writeACK_2clk_check: assert property(writeEnable_one_writeACK_2clk) 
  else $display($stime,,,"\t\tWRITEENABLE WRITEACK FAIL:: The value of writeEnable changed to not(1) while writeAck was stable at 0\n");


endmodule
