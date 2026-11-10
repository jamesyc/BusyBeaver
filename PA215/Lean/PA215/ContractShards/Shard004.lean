import PA215.ContractShards.Shard004Part0
import PA215.ContractShards.Shard004Part1
import PA215.ContractShards.Shard004Part2
import PA215.ContractShards.Shard004Part3
import PA215.ContractShards.Shard004Part4
import PA215.ContractShards.Shard004Part5
import PA215.ContractShards.Shard004Part6
import PA215.ContractShards.Shard004Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard004Part0.records ++
  PA215.ContractShards.Shard004Part1.records ++
  PA215.ContractShards.Shard004Part2.records ++
  PA215.ContractShards.Shard004Part3.records ++
  PA215.ContractShards.Shard004Part4.records ++
  PA215.ContractShards.Shard004Part5.records ++
  PA215.ContractShards.Shard004Part6.records ++
  PA215.ContractShards.Shard004Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard004
