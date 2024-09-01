from BaseEnvironment import BaseEnvironment
import cocotb

class Test1(BaseEnvironment):
    def __init__(self, dut):
        BaseEnvironment.__init__(self, dut)

    async def test(self):
        await BaseEnvironment.start(self)
        await BaseEnvironment.read_Register(self, addr=0x9, expected_data=0xBADEFACE)

@cocotb.test()
async def tests(dut):
    Test = Test1(dut)
    await Test.test() #run test