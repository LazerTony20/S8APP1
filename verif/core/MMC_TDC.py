import time

from MMC_CRC8 import DataValidMonitor_Template
import cocotb
from typing import Any, Dict, List
from cocotb.handle import SimHandleBase
from cocotb.queue import Queue
from cocotb.triggers import RisingEdge
from cocotb.log import SimLog

class MMC_TDC:
    def __init__(self, logicblock_instance: SimHandleBase):
        self.dut = logicblock_instance
        self.log = SimLog("cocotb.MMC.%s" % (type(self).__qualname__))

        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.clk,
            datas=dict(hasEvent=self.dut.o_hasEvent,
                       busy=self.dut.o_busy,
                       trigger=self.dut.i_trigger,
                       chanID=self.dut.o_chanID,
                       timestamp=self.dut.o_timestamp,
                       pulseWidth=self.dut.o_pulseWidth,)
        )

        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.o_hasEvent,
            datas=dict(timestamp=self.dut.o_timestamp,
                       pulseWidth=self.dut.o_pulseWidth,)
        )

        self._checkercoro = None
    def start(self) -> None:
        """Starts monitors, model, and checker coroutine"""
        if self._checkercoro is not None:
            raise RuntimeError("Monitor already started")
        self.input_mon.start()
        self.output_mon.start()
        self._checkercoro = cocotb.start_soon(self._checker())

    def stop(self) -> None:
        """Stops everything"""
        if self._checkercoro is None:
            raise RuntimeError("Monitor never started")
        self.input_mon.stop()
        self.output_mon.stop()
        self._checkercoro.kill()
        self._checkercoro = None

    # Model, modify as needed.
    def model(self, pulseWidth):
        # equivalent model to HDL code
        if pulseWidth > 5000:
            pulseWidth = 5000
        return pulseWidth

    # Insert logic to decide when to check the model against the HDL result.
    # then compare output monitor result with model result
    # This example might not work every time.
    async def _checker(self) -> None:
        TIMEFACTOR = 10
        clk_count = 99 # Adjust timing with _init_signals
        pulse_width = 0
        timestamp = 0
        #await cocotb.triggers.ClockCycles(self.dut.clk, clk_count, rising=True)
        while True:
            val = 0
            val2 = 0
            try:
                val = self.input_mon.values.get_nowait()
                if val["trigger"].integer == 1 + timestamp:  # Detect trigger rising edge.
                    timestamp = clk_count * TIMEFACTOR
                if (val["trigger"].integer == pulse_width) and timestamp:  # Detect trigger falling edge.
                    pulse_width = self.model((clk_count * TIMEFACTOR) - timestamp)
                    val2 = await self.output_mon.values.get()
                    rec_timestamp = (val2["timestamp"].integer * 40) / 1000
                    rec_pulse_width = (val2["pulseWidth"].integer * 40) / 1000
                    assert rec_timestamp == timestamp
                    assert rec_pulse_width == pulse_width
                clk_count += 1
            except cocotb.queue.QueueEmpty:
                self.log = SimLog("Queue empty")
            if timestamp == 0: # Check if an interpolation started.
                # Testing inactivity (how)
                assert self.dut.o_busy == 0
            await cocotb.triggers.ClockCycles(self.dut.clk, 1, rising=True)

        return True

    """
                Récupérer toutes les valeurs dans une Queue:
                                    SamplesList = []
                                        while(not self.mon.values.empty()):
                                            SamplesList.append(self.mon.values.get_nowait())

                Prendre la valeur d'un signal, au nième élément seulement
                SamplesList[N]["NomDictionnaire"]

                Prendre la valeur d'un signal, au nième élément, et changer son type pour un entier
                SamplesList[N]["NomDictionnaire"].integer

                Extraire toutes les valeurs d'un signal d'une telle liste:
                SignalSamples = [d['NomSignal'] for d in SamplesList]
                --> depuis https://stackoverflow.com/questions/7271482/getting-a-list-of-values-from-a-list-of-dicts

                Même chose, mais en changeant aussi les valeur d'un bus pour des entiers
                ValueList = [d['NomSignal'].integer for d in expected_inputs]

                Lire une valeur dès que disponible, attendre sinon
                actual = await self.mon.values.get()

                # compare expected with actual using assertions. 
                assert actual["SignalC"] == expected
                """