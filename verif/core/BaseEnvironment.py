# Imports
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import build_command_message, get_expected_crc, print_cocotb_BinaryValue
from cocotb.log import SimLog
from MMC_CRC8 import MMC_CRC8
from MMC_TDC import MMC_TDC
import os
import pydevd_pycharm

class BaseEnvironment:
    UART_DATA_MASK = 0x0000FFFFFFFF
    UART_CRC_MASK  = 0xFFFF00000000
    def __init__(self, dut):
        self._dut = dut
        self._MMC = self._init_MMC(dut)
    # Operations methods:
    async def start(self):
        print("Uart instance demo")
        # Starting local debug server
        PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')

        print(PYCHARMDEBUG)

        # if (PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=9696, stdoutToServer=True, stderrToServer=True)
        await self._init_signals()    # Initialize the bench signals.
        self._run_MMC()         # Run all MMCs.

    def stop(self):
        self._stop_MMC()
        # Stoping signals?

        return 1

    async def _init_signals(self):
        # start a clock signal (100MHZ)
        await cocotb.start(Clock(self._dut.clk, 10, units='ns').start())
        # set a signal to some value
        self._dut.reset.value = 1
        self._dut.inst_tdc_channel_1.reset.value = 1
        self._dut.in_sig.value = 1
        self._dut.clkMHz.value = 1
        self._dut.resetCyclic.value = 1
        self._dut.inst_tdc_channel_0.i_enable_channel.value = 0
        self._dut.inst_tdc_channel_1.i_enable_channel.value = 0
        self._dut.inst_tdc_channel_0.i_trigger.value = 0
        # wait for 100 clock periods
        await cocotb.triggers.ClockCycles(self._dut.clk, 100, rising=True)
    def _init_MMC(self, dut):
        MMCs = []
        MMCs.append(MMC_CRC8(dut.inst_packet_merger.inst_crc_calc))
        MMCs.append(MMC_TDC(dut.inst_tdc_channel_0))
        #MMCs.append(MMC_TDC(dut.inst_tdc_channel_1))
        # Add other MMCs to add to list here
        return MMCs

    # Run all MMCs
    def _run_MMC(self):
        for MMC in self._MMC:
            MMC.start()
        return 1
    # Stop all MMCs
    def _stop_MMC(self):
        for MMC in self._MMC:
            MMC.stop()
        return 1
    # Virtual test method. To be implemented by user.
    def test(self):
        raise NotImplementedError()
    # Agent methods:
    async def read_Register(self, addr, expected_data):
        data = [1]
        # Assembling packet to send.
        read_command = 0x0      # hex code for read command
        packet_binary = self._assemble_UART_packet(read_command,addr,0x0)
        # Set sequence for communication start
        self._dut.reset.value = 0  # Set reset signal to 0
        # wait for 100 clock periods
        await cocotb.triggers.ClockCycles(self._dut.clk, 100, rising=True)
        # Driver and Sink for the dut UART RX/TX channels
        uart_driver = UartSource(self._dut.in_sig, baud=1000000, bits=8)
        uart_sink = UartSink(self._dut.out_sig, baud=1000000, bits=8)
        # Start thread for the reply function for the expected UART response.
        Task_returnMessage = await cocotb.start(self._wait_reply(uart_sink, data))
        # [DEBUG] Print cocotb value demo function. Uncomment if desired.
        # print_cocotb_BinaryValue(packet_binary)
        # Send packet, then wait for transaction to complete
        await uart_driver.write(packet_binary.buff)
        await uart_driver.wait()
        # Wait for response to complete or for timeout.
        await Task_returnMessage
        # Automatically operate a check on the received data.
        self._validate_Data(expected_data, self._decapsulate(data[0], self.UART_DATA_MASK))
        return data[0]

    async def _wait_reply(self, uart_sink, data):
        # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
        for x in range(0, 100):
            if (uart_sink.count() >= 7):  ## 6 octets du message + le CRC
                break;
            await cocotb.triggers.ClockCycles(self._dut.clk, 1000, rising=True)

        if (x == 99):
            print("Timeout")
            logger = SimLog("cocotb.Test")
            logger.info("Timeout for wait reply")
            raise RuntimeError("Timeout for wait reply")
            # or use plain assert.
            # assert False, "Timeout for wait reply"
            return None

        else:
            # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
            message_bytes = bytes(await uart_sink.read(count=6))
            message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
            print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
            print("0x{0:0{width}x}".format(message.integer, width=12))
            data = message.integer
            return message
    async def write_Register(self, addr, data):
        write_command = 0x1     # hex code for write command
        packet_binary = self._assemble_UART_packet(write_command, addr, data)
        # Set sequence for communication start.
        self._dut.reset.value = 0  # Set reset signal to 0
        # wait for 100 clock periods.
        await cocotb.triggers.ClockCycles(self._dut.clk, 100, rising=True)
        # Driver and Sink for the dut UART RX/TX channels.
        uart_driver = UartSource(self._dut.in_sig, baud=1000000, bits=8)
        # [DEBUG] Print cocotb value demo function. Uncomment if desired.
        # print_cocotb_BinaryValue(packet_binary)
        # Send packet, then wait for transaction to complete
        await uart_driver.write(packet_binary.buff)
        await uart_driver.wait()
        # Return sent CRC value.
        return self._decapsulate(packet_binary.integer, self.UART_CRC_MASK)

    def _decapsulate(self, data, mask):
        return data & mask

    def _validate_Data(seld, expected_value, received_value):
        if (expected_value != received_value):
            logger = SimLog("cocotb.Test")
            logger.info("Recieved value is not equal to expected value")
        else:
            logger = SimLog("cocotb.Test")
            logger.info("Recieved value is equal to expected value")
    def _assemble_UART_packet(self, command, addr, data):
        message = build_command_message(command, addr, data)
        crc = get_expected_crc(message.buff)
        packet = message.integer + (crc << 48)
        return cocotb.binary.BinaryValue(value=packet, n_bits=56, bigEndian=False)
    async def sendPulse(self, start_delay, length_clk):
        self._dut.inst_tdc_channel_1.reset.value = 0
        await cocotb.triggers.ClockCycles(self._dut.clk, start_delay, rising=True)  # Arbitrary amount of time waiting.
        self._dut.inst_tdc_channel_0.i_enable_channel.value = 1
        self._dut.inst_tdc_channel_1.i_enable_channel.value = 1
        self._dut.inst_tdc_channel_0.i_trigger.value = 1
        self._dut.inst_tdc_channel_1.i_trigger.value = 1
        await cocotb.triggers.ClockCycles(self._dut.clk, length_clk, rising=True)
        self._dut.inst_tdc_channel_0.i_trigger.value = 0
        self._dut.inst_tdc_channel_1.i_trigger.value = 0
        await cocotb.triggers.ClockCycles(self._dut.clk, 230, rising=True)   # Arbitrary amount of time waiting.