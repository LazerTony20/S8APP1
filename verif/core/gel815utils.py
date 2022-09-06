import cocotb
from bitarray.util import int2ba, ba2int




# Expects cocotb.binary.BinaryValue() argument
def gei815_print_cocotb_BinaryValue(SomeValue):
    print("print Cocotb binary string : " + SomeValue.binstr)
    print("print Cocotb integer       : " + "{}".format(SomeValue.integer))
    print("print Cocotb integer in hex: " + "0x{0:{width}x}".format(SomeValue.integer, width=8))
    print("print Cocotb byte buffer ", end='');  print(SomeValue.buff)
    print("print Cocotb byte byte per byte, seen as a serie of int   : ");
    for item in SomeValue.buff:
        print("\t0x{0:2x} ".format(item), end='') # hexadecimal
        print(item)  # decimal
    print()

def gei815_build_command_message(command, addr, data):
    message = (command << 43) + (addr << 32) + data
    return cocotb.binary.BinaryValue(value=message, n_bits=48, bigEndian=False)

"""
CRC utility
Usage example
    data = prepare_data(0, 9, 0x345678)  # Reading reg at address 0
    some_bytes = data.to_bytes(6, sys.byteorder)
    resultingCRC = get_expected_crc(some_bytes)
    my_bytearray = bytearray(some_bytes)
    my_bytearray.append(resultingCRC)
    await uart_source.write(my_bytearray)
"""

CRC8_START = 0x0D
CRC_POLY = 0xC6

def gei815_calculateCRC8(data, current_crc):
    crc = int2ba(current_crc, 8)
    data_bits = int2ba(data, 8)
    poly = int2ba(CRC_POLY, 8)
    for j in range(7, -1, -1):
        if crc[7] != data_bits[j]:
            crc = (crc >> 1) ^ poly
        else:
            crc >>= 1
    return ba2int(crc)


def gei815_get_expected_crc(value):
    current_crc = CRC8_START
    print(value)
    for b in value:
        current_crc = gei815_calculateCRC8(b, current_crc)

    return current_crc
