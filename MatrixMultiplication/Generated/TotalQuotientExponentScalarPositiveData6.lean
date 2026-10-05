import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive6

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1405, 1415, 1417, 1419, 1421, 1423,
    1425, 1427, 1429, 1431, 1433, 1435,
    1439, 1441, 1443, 1451, 1465, 1469,
    1475, 1479, 1485, 1489, 1491, 1495,
    1503, 1509, 1513, 1521, 1523, 1527,
    1529, 1533, 1545, 1547, 1551, 1557,
    1565, 1569, 1571, 1573, 1577, 1581,
    1589, 1593, 1595, 1601, 1605, 1607,
    1615, 1617, 1619, 1637, 1639, 1645,
    1649, 1663, 1665, 1667, 1669, 1673,
    1675, 1679, 1683, 1685
  ]

def coefficients : Array ℕ := #[
    12058120683520, 103079215104, 15032385536, 20948702986240, 1357209665536, 471570229231616,
    143280108994560, 85899345920, 457809154015232, 68719476736, 33346126086144, 16426102423552,
    175629802668032, 68719476736, 10977936408576, 43529493544960, 180388626432, 549755813888,
    272659556335616, 781684047872, 59614146068480, 206158430208, 68719476736, 231928233984,
    68719476736, 137438953472, 463856467968, 788667664695296, 710439130365952, 143611895218176,
    962072674304, 137438953472, 152969555214336, 206158430208, 515396075520, 378987914199040,
    6734508720128, 266614389866496, 154618822656, 162491497709568, 292536664981504, 274877906944,
    242159919824896, 103079215104, 273778395316224, 59098749992960, 265474076049408, 257698037760,
    2310692405248, 68719476736, 3994319585280, 19043884990464, 60129542144, 5772436045824,
    481036337152, 1145588036927488, 962072674304, 103079215104, 996432412672, 115996329246720,
    68719476736, 107374182400, 34359738368, 57896159150080
  ]

def scales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10
  ]

abbrev Term := Fin 64
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 2005658115527 / 1000000000000

theorem floor_le_fast : floor ≤ fastLower := by
  norm_num [floor, fastLower, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
    argument, coefficient, scale, arguments, coefficients, scales,
    MatrixMultiplication.FastDyadicLog.numeratorLogLower,
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper,
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower,
    MatrixMultiplication.FastDyadicLog.fastLogTwoUpper,
    reducedArgument,
    AlgebraicComplexity.Analysis.logRatioLower,
    AlgebraicComplexity.Analysis.logRatioUpper,
    AlgebraicComplexity.Analysis.atanhPartial,
    AlgebraicComplexity.Analysis.atanhRemainder, Fin.sum_univ_succ,
    Finset.sum_range_succ, mass]

theorem exact_bound : floor ≤ exact := by
  exact floor_le_fast.trans (fastLogSumLowerWithScale_le_logSum 8 55 argument coefficient scale scales_valid)

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive6
