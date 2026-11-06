import PA215.CertifiedContracts
import PA215.Census.C006
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006Part6
open PA215.Contracts PA215.Census

def original870 : RawOriginal := C006.records[102]'(by decide)
theorem original_id870 : original870.index = 870 := by decide

def c870 : Contract := original870.toContract.get (by decide)
theorem binding870 : original870.toContract = some c870 := rfl

theorem checked870 : check 4000 c870 = true := by decide

def original871 : RawOriginal := C006.records[103]'(by decide)
theorem original_id871 : original871.index = 871 := by decide

def c871 : Contract := original871.toContract.get (by decide)
theorem binding871 : original871.toContract = some c871 := rfl

theorem checked871 : check 4000 c871 = true := by decide

def original872 : RawOriginal := C006.records[104]'(by decide)
theorem original_id872 : original872.index = 872 := by decide

def c872 : Contract := original872.toContract.get (by decide)
theorem binding872 : original872.toContract = some c872 := rfl

theorem checked872 : check 4000 c872 = true := by decide

def original873 : RawOriginal := C006.records[105]'(by decide)
theorem original_id873 : original873.index = 873 := by decide

def c873 : Contract := original873.toContract.get (by decide)
theorem binding873 : original873.toContract = some c873 := rfl

theorem checked873 : check 4000 c873 = true := by decide

def original874 : RawOriginal := C006.records[106]'(by decide)
theorem original_id874 : original874.index = 874 := by decide

def c874 : Contract := original874.toContract.get (by decide)
theorem binding874 : original874.toContract = some c874 := rfl

theorem checked874 : check 4000 c874 = true := by decide

def original875 : RawOriginal := C006.records[107]'(by decide)
theorem original_id875 : original875.index = 875 := by decide

def c875 : Contract := original875.toContract.get (by decide)
theorem binding875 : original875.toContract = some c875 := rfl

theorem checked875 : check 4000 c875 = true := by decide

def original876 : RawOriginal := C006.records[108]'(by decide)
theorem original_id876 : original876.index = 876 := by decide

def c876 : Contract := original876.toContract.get (by decide)
theorem binding876 : original876.toContract = some c876 := rfl

theorem checked876 : check 4000 c876 = true := by decide

def original877 : RawOriginal := C006.records[109]'(by decide)
theorem original_id877 : original877.index = 877 := by decide

def c877 : Contract := original877.toContract.get (by decide)
theorem binding877 : original877.toContract = some c877 := rfl

theorem checked877 : check 4000 c877 = true := by decide

def original878 : RawOriginal := C006.records[110]'(by decide)
theorem original_id878 : original878.index = 878 := by decide

def c878 : Contract := original878.toContract.get (by decide)
theorem binding878 : original878.toContract = some c878 := rfl

theorem checked878 : check 4000 c878 = true := by decide

def original879 : RawOriginal := C006.records[111]'(by decide)
theorem original_id879 : original879.index = 879 := by decide

def c879 : Contract := original879.toContract.get (by decide)
theorem binding879 : original879.toContract = some c879 := rfl

theorem checked879 : check 4000 c879 = true := by decide

def original880 : RawOriginal := C006.records[112]'(by decide)
theorem original_id880 : original880.index = 880 := by decide

def c880 : Contract := original880.toContract.get (by decide)
theorem binding880 : original880.toContract = some c880 := rfl

theorem checked880 : check 4000 c880 = true := by decide

def original881 : RawOriginal := C006.records[113]'(by decide)
theorem original_id881 : original881.index = 881 := by decide

def c881 : Contract := original881.toContract.get (by decide)
theorem binding881 : original881.toContract = some c881 := rfl

theorem checked881 : check 4000 c881 = true := by decide

def original882 : RawOriginal := C006.records[114]'(by decide)
theorem original_id882 : original882.index = 882 := by decide

def c882 : Contract := original882.toContract.get (by decide)
theorem binding882 : original882.toContract = some c882 := rfl

theorem checked882 : check 4000 c882 = true := by decide

def original883 : RawOriginal := C006.records[115]'(by decide)
theorem original_id883 : original883.index = 883 := by decide

def c883 : Contract := original883.toContract.get (by decide)
theorem binding883 : original883.toContract = some c883 := rfl

theorem checked883 : check 4000 c883 = true := by decide

def original884 : RawOriginal := C006.records[116]'(by decide)
theorem original_id884 : original884.index = 884 := by decide

def c884 : Contract := original884.toContract.get (by decide)
theorem binding884 : original884.toContract = some c884 := rfl

theorem checked884 : check 4000 c884 = true := by decide

def original885 : RawOriginal := C006.records[117]'(by decide)
theorem original_id885 : original885.index = 885 := by decide

def c885 : Contract := original885.toContract.get (by decide)
theorem binding885 : original885.toContract = some c885 := rfl

theorem checked885 : check 4000 c885 = true := by decide

def records : List Certified := [
  ⟨870, c870, 4000, checked870⟩,
  ⟨871, c871, 4000, checked871⟩,
  ⟨872, c872, 4000, checked872⟩,
  ⟨873, c873, 4000, checked873⟩,
  ⟨874, c874, 4000, checked874⟩,
  ⟨875, c875, 4000, checked875⟩,
  ⟨876, c876, 4000, checked876⟩,
  ⟨877, c877, 4000, checked877⟩,
  ⟨878, c878, 4000, checked878⟩,
  ⟨879, c879, 4000, checked879⟩,
  ⟨880, c880, 4000, checked880⟩,
  ⟨881, c881, 4000, checked881⟩,
  ⟨882, c882, 4000, checked882⟩,
  ⟨883, c883, 4000, checked883⟩,
  ⟨884, c884, 4000, checked884⟩,
  ⟨885, c885, 4000, checked885⟩]

end PA215.ContractShards.Shard006Part6
