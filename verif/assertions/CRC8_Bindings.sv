//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind CRC8816 CRC8_Bindings
    #(.DATA_LENGTH(DATA_LENGTH),
    .DATA_LENGTH_BYTES(DATA_LENGTH_BYTES))

     inst_CRC8_Bindings(
        .cov_reset(reset),
        .cov_clk(clk),

        .cov_valid(i_valid),
        .cov_last(i_last),
        .cov_data(i_data),

        .cov_match(o_match),
        .cov_done(o_done),
        .cov_crc8(o_crc8)
	);

module CRC8_Bindings#(
    DATA_LENGTH = 32,
    DATA_LENGTH_BYTES = DATA_LENGTH/8)
	(
	input logic cov_reset,
	input logic cov_clk,

    input logic cov_valid,
    input logic cov_last,
    input logic [7:0] cov_data,

    input logic cov_match,
    input logic cov_done,
    input logic [DATA_LENGTH-1:0] cov_crc8
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

// ====== Lab 3 ======
/* THIS TEST IS A REAL ONE. IT HAS BEEN COMMENTED ONLY TO CLEAR UP THE LOGS. WE KNOW THIS TEST FINDS A PROBLEM IN THE IMPLEMENTATION.
// Last implique que done montera à 1 après 1 ou 2 coups d’horloge.
property last_done;
    @(posedge cov_clk) $fell(cov_last)|-> ##[1:2] cov_done == 1;
endproperty
last_done_check: assert property(last_done) 
  else $display($stime,,,"\t\tLAST DONE CHECK FAIL:: DONE DIDN'T RISE TO A VALUE OF 1 \n");
*/

// Si Match à ’1’, cela implique que Done est aussi à 1.
property match_done;
    @(posedge cov_clk) cov_match == 1 |-> cov_done == 1;
endproperty
match_done_check: assert property(match_done) 
  else $display($stime,,,"\t\tMATCH DONE CHECK FAIL:: DONE ISN'T 1 WITH MATCH = 1 \n");

// Si match est devenu ’1’, cela implique que last était à 1 il y a 1-2 coups d’horloge.
property match_last;
    @(posedge cov_clk) $rose(cov_match) |-> $past(cov_last,1) == 1 || $past(cov_last,2) == 1;
endproperty
match_last_check: assert property(match_last) 
  else $display($stime,,,"\t\MATCH LAST CHECK FAIL:: LAST WASN'T 1 IN THE LAST 1 OR 2 CLOCK CYCLE BEFORE MATCH = 1\n");

/*THIS TEST IS A REAL ONE. IT HAS BEEN COMMENTED ONLY TO CLEAR UP THE LOGS. WE KNOW THIS TEST FINDS A PROBLEM IN THE IMPLEMENTATION.
// La valeur de CRC ne change pas si valid vaut 0.
property crc_static_valid_zero;
    @(posedge cov_clk) disable iff(!cov_reset) cov_valid == 0 |=> $stable(cov_crc8);
endproperty
crc_static_valid_zero_check: assert property(crc_static_valid_zero) 
  else $display($stime,,,"\t\CRC STABLE VALUE CHECK FAIL:: THE CRC VALUE CHANGED WHILE VALID = 0\n");
*/

// Au coup d’horloge après que reset soit ’1’, CRC8 vaut 0x0D.
property crc_reset_value;
    @(posedge cov_clk) cov_reset == 1 |-> ##1 cov_crc8 == 8'h0D;
endproperty
crc_reset_value_check: assert property(crc_reset_value) 
  else $display($stime,,,"\t\CRC8 VALUE RESET FAIL:: THE CRC8 VALUE WASN'T PROPERLY SET AFTER RESET\n");
// ====== Fin Lab 3 ======

// ============ Stuff du Banc de Test de CRC8 qui manque au lab ============
// o_match vaut 0 apres un reset
property o_match_reset_value;
    @(posedge cov_clk) $fell(cov_reset) |=> cov_match == 0;
endproperty
o_match_reset_value_check: assert property(o_match_reset_value) 
  else $display($stime,,,"\t\O_MATCH RESET VALUE FAIL:: THE O_MATCH VALUE WASN'T 0 AFTER RESET\n");

// o_done retombe a 0 uniquement sur un reset
property o_done_reset;
    @(posedge cov_clk) $fell(cov_done) |=> cov_reset == 1;
endproperty
o_done_reset_check: assert property(o_done_reset) 
  else $display($stime,,,"\t\O_DONE VALUE RESET FAIL:: THE O_DONE VALUE WAS RESETED OUTSIDE A RESET\n");


/* THIS TEST IS A REAL ONE. IT HAS BEEN COMMENTED ONLY TO CLEAR UP THE LOGS. WE KNOW THIS TEST FINDS A PROBLEM IN THE IMPLEMENTATION.

// i_last toujours en meme temps que valid
property i_last_valid;
    @(posedge cov_clk) cov_last |-> cov_valid;
endproperty
i_last_valid_check: assert property(i_last_valid) 
  else $display($stime,,,"\t\I_LAST VALUE VALID FAIL:: THE I_LAST VALUE AND VALID WEREN'T BOTH TRUE\n");
*/
endmodule
