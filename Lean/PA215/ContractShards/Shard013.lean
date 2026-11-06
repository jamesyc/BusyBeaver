import PA215.ContractShards.Shard013Part0
import PA215.ContractShards.Shard013Part1
import PA215.ContractShards.Shard013Part2
import PA215.ContractShards.Shard013Part3
import PA215.ContractShards.Shard013Part4
import PA215.ContractShards.Shard013Part5
import PA215.ContractShards.Shard013Part6
import PA215.ContractShards.Shard013Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard013
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard013Part0.records ++
  PA215.ContractShards.Shard013Part1.records ++
  PA215.ContractShards.Shard013Part2.records ++
  PA215.ContractShards.Shard013Part3.records ++
  PA215.ContractShards.Shard013Part4.records ++
  PA215.ContractShards.Shard013Part5.records ++
  PA215.ContractShards.Shard013Part6.records ++
  PA215.ContractShards.Shard013Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard013
