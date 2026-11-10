import PA215.ContractShards.Shard005Part0
import PA215.ContractShards.Shard005Part1
import PA215.ContractShards.Shard005Part2
import PA215.ContractShards.Shard005Part3
import PA215.ContractShards.Shard005Part4
import PA215.ContractShards.Shard005Part5
import PA215.ContractShards.Shard005Part6
import PA215.ContractShards.Shard005Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard005
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard005Part0.records ++
  PA215.ContractShards.Shard005Part1.records ++
  PA215.ContractShards.Shard005Part2.records ++
  PA215.ContractShards.Shard005Part3.records ++
  PA215.ContractShards.Shard005Part4.records ++
  PA215.ContractShards.Shard005Part5.records ++
  PA215.ContractShards.Shard005Part6.records ++
  PA215.ContractShards.Shard005Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard005
