import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import build_command_message, get_expected_crc, print_cocotb_BinaryValue  #verif.core.
from cocotb.log import SimLog
from MMC_CRC8 import MMC_CRC8

import os
import pydevd_pycharm


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def cocotbext_uart_demo(dut):
    print("Uart instance demo")
    #Starting local debug server
    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')

    print(PYCHARMDEBUG)

    #if (PYCHARMDEBUG == "enabled"):
    pydevd_pycharm.settrace('localhost', port=9696, stdoutToServer=True, stderrToServer=True)

    # L2.E1 - Ajouter l'instanciation du MMC
    inst_MMC_CRC8 = MMC_CRC8(dut.inst_packet_merger.inst_crc_calc)
    inst_MMC_CRC8.start()

    # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge
    await initSigs(dut)
    # Set sequence for communication start
    dut.reset.value = 0  # Set reset signal to 0
    # wait for 100 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 100, rising=True)

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    # L1.E4 - Start thread for the reply function for the expected UART response.
    Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink))

    # Generate arbitrary value to send on the UART
    command = build_command_message(0x0, 0x9, 0x0)
    crc = get_expected_crc(command.buff)
    packet = command.integer + (crc << 48)
    SomeValue = cocotb.binary.BinaryValue(value=packet, n_bits=56, bigEndian=False)

    # Print cocotb value demo function. Uncomment if desired.
    print_cocotb_BinaryValue(SomeValue)

    # Send arbitrary value, then wait for transaction to complete
    await uart_driver.write(SomeValue.buff)
    await uart_driver.wait()
    # L1.E4 wait for response to complete or for timeout
    await Task_returnMessage

# L.E4 function to wait for response message
async def wait_reply(dut, uart_sink):

    # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
    for x in range(0, 100):
        if(uart_sink.count() >= 7): ## 6 octets du message + le CRC
            break;
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if(x == 99):
        print("Timeout")
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        raise RuntimeError("Timeout for wait reply")
        # or use plain assert.
        #assert False, "Timeout for wait reply"
        return None

    else:
        # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
        message_bytes = bytes(await uart_sink.read(count=6))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
        print("0x{0:0{width}x}".format(message.integer, width=12))
        validate_Data(0xbadeface, decapsulate(message.integer,0x0000FFFFFFFF))
        return message
async def initSigs(dut):
    # start a clock signal (100MHZ)
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())
    # set a signal to some value
    dut.reset.value = 1
    dut.in_sig.value = 1
    dut.clkMHz.value = 1
    dut.resetCyclic.value = 1
    # wait for 100 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 100, rising=True)

def decapsulate(data, mask):
    return data & mask
def validate_Data(expected_value, received_value):
    if(expected_value != received_value):
        logger = SimLog("cocotb.Test")
        logger.info("Recieved value is not equal to expected value")
    else:
        logger = SimLog("cocotb.Test")
        logger.info("Recieved value is equal to expected value")
