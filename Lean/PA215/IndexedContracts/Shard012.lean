import PA215.IndexedContracts.Shard012Part0
import PA215.IndexedContracts.Shard012Part1
import PA215.IndexedContracts.Shard012Part2
import PA215.IndexedContracts.Shard012Part3
import PA215.IndexedContracts.Shard012Part4
import PA215.IndexedContracts.Shard012Part5
import PA215.IndexedContracts.Shard012Part6
import PA215.IndexedContracts.Shard012Part7
namespace PA215.IndexedContracts.Shard012
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard012Part0.records ++
  PA215.IndexedContracts.Shard012Part1.records ++
  PA215.IndexedContracts.Shard012Part2.records ++
  PA215.IndexedContracts.Shard012Part3.records ++
  PA215.IndexedContracts.Shard012Part4.records ++
  PA215.IndexedContracts.Shard012Part5.records ++
  PA215.IndexedContracts.Shard012Part6.records ++
  PA215.IndexedContracts.Shard012Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard012Part0.exact_ids, PA215.IndexedContracts.Shard012Part1.exact_ids, PA215.IndexedContracts.Shard012Part2.exact_ids, PA215.IndexedContracts.Shard012Part3.exact_ids, PA215.IndexedContracts.Shard012Part4.exact_ids, PA215.IndexedContracts.Shard012Part5.exact_ids, PA215.IndexedContracts.Shard012Part6.exact_ids, PA215.IndexedContracts.Shard012Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard012
