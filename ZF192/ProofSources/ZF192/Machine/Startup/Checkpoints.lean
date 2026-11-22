module
public import ZF192.Machine.Startup.Replay

@[expose] public section

namespace M192.Startup

/-- Boundary configurations of the blank run, encoded with the bit closest to
the head in the least significant position of each tape word. -/
def checkpoint1 : Packed := (117, 0x55edef96e6, 0x3f36f7fdfbbffff3)
def checkpoint2 : Packed := (128, 0x16bd3fffffb6e36, 0xfcdbdff7eeffffcd93f36f6f3f387e)
def checkpoint3 : Packed := (129, 0x157aaa7ffffffffff, 0x3f36f7fdfbbffff364fcdbdbcfce1f907fff)
def checkpoint4 : Packed := (117, 0x5aaab9fff, 0xfcdbdff7eeffffcd93f36f6f3f387e6cfffffffffffffff)
def checkpoint5 : Packed := (157, 0x2aaab9fffffffffffffffffffff, 0x1f9b7bfefddffff9b27e6dede7e70fc)

end M192.Startup
