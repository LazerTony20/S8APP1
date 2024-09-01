# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0

# adapted from https://github.com/cocotb/cocotb/blob/stable/1.9/examples/matrix_multiplier/tests/test_matrix_multiplier.py

from typing import Any, Dict, List

import cocotb
from cocotb.clock import Clock
from cocotb.handle import SimHandleBase
from cocotb.queue import Queue
from cocotb.triggers import RisingEdge
from cocotb.log import SimLog
from utilsVerif import get_expected_crc


class DataValidMonitor_Template:
    """
    Reusable Monitor of one-way control flow (data/valid) streaming data interface

    Args
        clk: clock signal
        valid: control signal noting a transaction occured
        datas: named handles to be sampled when transaction occurs
    """

    def __init__(
            self, clk: SimHandleBase, valid: SimHandleBase, datas: Dict[str, SimHandleBase]
    ):
        self.values = Queue[Dict[str, int]]()
        self._clk = clk
        self._valid = valid
        self._datas = datas
        self._coro = None  # is monitor running? False if "None"

        self.log = SimLog("cocotb.Monitor.%s" % (type(self).__qualname__))

    def start(self) -> None:
        """Start monitor"""
        if self._coro is not None:
            raise RuntimeError("Monitor already started")
        self._coro = cocotb.start_soon(self._run())

    def stop(self) -> None:
        """Stop monitor"""
        if self._coro is None:
            raise RuntimeError("Monitor never started")
        self._coro.kill()
        self._coro = None

    async def _run(self) -> None:
        while True:
            await RisingEdge(self._clk)
            # this condition decides when to record the signal states
            if self._valid.value.binstr != "1":
                # skip whatever comes after, and start the while loop again
                continue
            # store the samples, as formatted by the _sample method
            self.values.put_nowait(self._sample())

    def _sample(self) -> Dict[str, Any]:
        """
        Samples the data signals and builds a transaction object

        Return value is what is stored in queue. Meant to be overriden by the user.
        """
        # possible messages to test monitor
        # self.log.info("use this to print some information at info level")
        self.log.info({name: handle.value for name, handle in self._datas.items()})

        # for loop going through all the values in the signals to sample (see constructor)
        return {name: handle.value for name, handle in self._datas.items()}


class MMC_CRC8:
    """
    Reusable checker of a checker instance

    Args
        logicblock_instance: handle to an instance of a logic block
    """

    def __init__(self, logicblock_instance: SimHandleBase):
        self.dut = logicblock_instance
        self.log = SimLog("cocotb.MMC.%s" % (type(self).__qualname__))

        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.i_valid,
            datas=dict(i_data=self.dut.i_data,
                       i_last=self.dut.i_last),
        )

        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.o_done,
            datas=dict(crc=self.dut.o_crc8,
                       match=self.dut.o_match)
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
    def model(self, echantillons):
        # equivalent model to HDL code
        crc = echantillons.pop(len(echantillons)-1).integer     # Remove the CRC from the list. Only data remains.
        echantillons.pop(len(echantillons) - 1)     # Removing input CRC from data
        crc_calc = get_expected_crc(echantillons)
        if crc != crc_calc: # Compare the two CRCs
            return False
        else:
            return True

    # Insert logic to decide when to check the model against the HDL result.
    # then compare output monitor result with model result
    # This example might not work every time.
    async def _checker(self) -> None:
        while True:
            # dummy await, allows to run without checker implementation and verify monitors
            # await cocotb.triggers.ClockCycles(self.dut.clk, 1000, rising=True)
            actual = await self.output_mon.values.get()
            SamplesList = []
            while (not self.input_mon.values.empty()):
                SamplesList.append(self.input_mon.values.get_nowait())
            SignalSamples = [d['i_data'].integer for d in SamplesList]  # Extracting all input data signals.
            SignalSamples.append(actual["crc"])  # Adding the received CRC data at the end of the list.
            assert actual["match"] == self.model(SignalSamples)  # Compute and compare CRCs. Check match reliability.
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
