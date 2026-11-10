import PA215.IndexedContracts.Shard011Part0
import PA215.IndexedContracts.Shard011Part1
import PA215.IndexedContracts.Shard011Part2
import PA215.IndexedContracts.Shard011Part3
import PA215.IndexedContracts.Shard011Part4
import PA215.IndexedContracts.Shard011Part5
import PA215.IndexedContracts.Shard011Part6
import PA215.IndexedContracts.Shard011Part7
namespace PA215.IndexedContracts.Shard011
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard011Part0.records ++
  PA215.IndexedContracts.Shard011Part1.records ++
  PA215.IndexedContracts.Shard011Part2.records ++
  PA215.IndexedContracts.Shard011Part3.records ++
  PA215.IndexedContracts.Shard011Part4.records ++
  PA215.IndexedContracts.Shard011Part5.records ++
  PA215.IndexedContracts.Shard011Part6.records ++
  PA215.IndexedContracts.Shard011Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard011Part0.exact_ids, PA215.IndexedContracts.Shard011Part1.exact_ids, PA215.IndexedContracts.Shard011Part2.exact_ids, PA215.IndexedContracts.Shard011Part3.exact_ids, PA215.IndexedContracts.Shard011Part4.exact_ids, PA215.IndexedContracts.Shard011Part5.exact_ids, PA215.IndexedContracts.Shard011Part6.exact_ids, PA215.IndexedContracts.Shard011Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard011
