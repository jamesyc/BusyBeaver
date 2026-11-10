import PA215.IndexedContracts.Shard037Part0
import PA215.IndexedContracts.Shard037Part1
import PA215.IndexedContracts.Shard037Part2
import PA215.IndexedContracts.Shard037Part3
import PA215.IndexedContracts.Shard037Part4
import PA215.IndexedContracts.Shard037Part5
import PA215.IndexedContracts.Shard037Part6
import PA215.IndexedContracts.Shard037Part7
namespace PA215.IndexedContracts.Shard037
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard037Part0.records ++
  PA215.IndexedContracts.Shard037Part1.records ++
  PA215.IndexedContracts.Shard037Part2.records ++
  PA215.IndexedContracts.Shard037Part3.records ++
  PA215.IndexedContracts.Shard037Part4.records ++
  PA215.IndexedContracts.Shard037Part5.records ++
  PA215.IndexedContracts.Shard037Part6.records ++
  PA215.IndexedContracts.Shard037Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756, 4757, 4758, 4759, 4760, 4761, 4762, 4763, 4764, 4765, 4766, 4767, 4768, 4769, 4770, 4771, 4772, 4773, 4774, 4775, 4776, 4777, 4778, 4779, 4780, 4781, 4782, 4783, 4784, 4785, 4786, 4787, 4788, 4789, 4790, 4791, 4792, 4793, 4794, 4795, 4796, 4797, 4798, 4799, 4800, 4801, 4802, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858, 4859, 4860, 4861, 4862, 4863, 4864, 4865, 4866, 4867, 4868, 4869] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard037Part0.exact_ids, PA215.IndexedContracts.Shard037Part1.exact_ids, PA215.IndexedContracts.Shard037Part2.exact_ids, PA215.IndexedContracts.Shard037Part3.exact_ids, PA215.IndexedContracts.Shard037Part4.exact_ids, PA215.IndexedContracts.Shard037Part5.exact_ids, PA215.IndexedContracts.Shard037Part6.exact_ids, PA215.IndexedContracts.Shard037Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard037
