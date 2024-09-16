from BaseEnvironment import BaseEnvironment
import cocotb
import random

class Test1(BaseEnvironment):
    def __init__(self, dut):
        BaseEnvironment.__init__(self, dut)

    async def test(self):
        r_pulse = random.randrange(1000)
        await BaseEnvironment.start(self)
        # RB.4.3
        await BaseEnvironment.read_Register(self, addr=0x9, expected_data=0xBADEFACE)
        # TDC.7.3
        await BaseEnvironment.sendPulse(self,10,750)
        # TDC.7.4
        await BaseEnvironment.sendPulse(self, 10, r_pulse)
        # TDC.11
        await BaseEnvironment.sendPulse(self, 10, 10)
        await BaseEnvironment.sendPulse(self, 1, 4) # Pulse to be ignored
        # End of test scenarios
        await BaseEnvironment.waitClk(self,250) # Delay to give time for the simulation to resolve

        """
        for i in range(8):  #Lecture de tous les registres
            await BaseEnvironment.read_Register(self, addr=i, expected_data=0x0)
        for i in range(8):  #Écriture de tous les registres
            await BaseEnvironment.write_Register(self, addr=i, data=0xFFFF1111)
        """

@cocotb.test()
async def tests(dut):
    Test = Test1(dut)
    await Test.test() #run test