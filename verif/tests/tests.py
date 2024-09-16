from BaseEnvironment import BaseEnvironment
import cocotb

class Test1(BaseEnvironment):
    def __init__(self, dut):
        BaseEnvironment.__init__(self, dut)

    async def test(self):
        await BaseEnvironment.start(self)
        await BaseEnvironment.read_Register(self, addr=0x9, expected_data=0xBADEFACE)   #Lecture du numéro de série.
        await BaseEnvironment.sendPulse(self,10,750)   # The two channels are tested at the same time.

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