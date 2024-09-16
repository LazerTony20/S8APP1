//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind TDC_dumb TDCCoverage inst_TDCCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_hasEvent(o_hasEvent),
	.cov_busy(o_busy),
	.cov_clear(i_clear),
	.cov_trigger(i_trigger),
	.cov_enable(i_enable_channel),
	.cov_TOT(o_pulseWidth),
	.cov_TS(o_timestamp)
	);

module TDCCoverage
	
	(
	input logic cov_reset,
	input logic cov_clk,
    	input logic cov_hasEvent,
	input logic cov_busy,
	input logic cov_clear,
    	input logic cov_trigger,
	input logic cov_enable,
	input logic [31:0] cov_TOT,
	input logic [31:0] cov_TS
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

covergroup covg_TDC
    @(negedge cov_clk && (cov_readEnable || cov_writeEnable) iff !cov_reset) ;
	option.name		= "cov_TDC";
    busy        : coverpoint cov_busy
    clear       : coverpoint cov_clear
    trigger     : coverpoint cov_trigger
    enable      : coverpoint cov_enable
    hasEvent    : coverpoint cov_hasEvent
    pulseWidth  : coverpoint cov_TOT
    timestamp   : coverpoint cov_TS
    }
endgroup

property check_reset;
    @(posedge cov_clk) cov_reset |-> (cov_busy == 0) && (cov_hasEvent == 0) && ((cov_TOT === 32'h0) || (cov_TOT === 32'hxxxxxxxx)) && ((cov_TS === 32'h0) || (cov_TS === 32'hxxxxxxxx));
endproperty
preqGnt: assert property (check_reset) else $display($stime,,,"\t\t %m FAIL");

property check_enable;
    @(posedge cov_clk) ##2 $rose(cov_reset) |=> $rose(cov_enable);
endproperty
assert property (check_enable) else $display($stime,,,"\t\t %m FAIL");

/* TODO: régler le F*CKING problème de fenêtre de ##[1:200]
sequence check_event_window;
    ##[1:200] cov_hasEvent;
endsequence


property check_hasEvent;
    @(posedge cov_clk) $fell(cov_trigger) |-> check_event_window;
endproperty
check_check_hasEvent : assert property (check_hasEvent) else $display($stime,,,"\t\t %m FAIL\n");
*/
/* TODO bug bizare avec ##[1:2]
property check_busy;
    @(posedge cov_clk) $rose(cov_trigger) |-> ##[1:2] cov_busy;
endproperty
assert_check_busy : assert property (check_busy) else $display($stime,,,"\t\t %m FAIL\n");
cov_check_busy  : cover property(check_busy);
*/

property check_pulseWidth;
    @(posedge cov_clk) !$stable(cov_TS) |-> cov_TOT < 32'h0001E849
endproperty
check_check_pulseWidth : assert property (check_pulseWidth) else $display($stime,,,"\t\t %m FAIL\n");
cov_check_busy  : cover property(check_pulseWidth);

property check_timestamp;
    @(posedge cov_clk) !$stable(cov_TS) |-> cov_TS < 32'hFFFFFFFF
endproperty
check_check_timestamp : assert property (check_timestamp) else $display($stime,,,"\t\t %m FAIL\n");
cov_check_timestamp  : cover property(check_timestamp);

property check_clear;
    @(posedge cov_clk) cov_clear |=> cov_hasEvent == 0
endproperty
check_check_clear : assert property (check_clear) else $display($stime,,,"\t\t %m FAIL\n");
cov_check_clear : cover property(check_clear);

property check_busy_to_0;
    @(posedge cov_clk) ##2 $fell(cov_trigger) |-> ##20 cov_busy;
endproperty
check_check_busy_to_0 : assert property (check_busy_to_0) else $display($stime,,,"\t\t %m FAIL\n");
cov_check_busy_to_0 : cover property(check_busy_to_0);

//On a pas le signal o_channel_ID...

endmodule
