import cocotb
from cocotb.clock import Clock
import os
#import cocotbext_uart_demo as cocoUart

import pydevd_pycharm


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def stuff(dut):
    print("Starting stuff welcome")

    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')

    print(PYCHARMDEBUG)

    if(PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=9696, stdoutToServer=True, stderrToServer=True)

    # start a clock signal (100MHZ)
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())
    # set a signal to some value
    dut.reset.value = 1
    dut.in_sig.value = 1
    dut.clkMHz.value = 1
    dut.resetCyclic.value = 1
    # wait for 100 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 100, rising=True)
    dut.reset.value = 0   #Set reset signal to 0
    # wait for 100 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 100, rising=True)

    # await cocoUart(dut)
    # fetch value from a signal in the dut
    fetch_value = dut.reset.value

    # Confirm type of read signal. Expected: cocotb.binary.BinaryValue
    print(type(fetch_value))


    # wait for 1000 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

