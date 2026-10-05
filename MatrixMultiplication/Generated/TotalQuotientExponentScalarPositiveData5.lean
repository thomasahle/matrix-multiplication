import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive5

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1199, 1201, 1203, 1205, 1207, 1209,
    1215, 1217, 1219, 1221, 1225, 1227,
    1229, 1231, 1233, 1239, 1241, 1243,
    1245, 1249, 1253, 1255, 1257, 1261,
    1267, 1273, 1275, 1277, 1281, 1287,
    1291, 1293, 1295, 1297, 1303, 1305,
    1307, 1309, 1311, 1313, 1317, 1319,
    1323, 1325, 1327, 1329, 1331, 1333,
    1335, 1339, 1341, 1345, 1347, 1349,
    1351, 1353, 1357, 1367, 1369, 1373,
    1375, 1377, 1381, 1389
  ]

def coefficients : Array ℕ := #[
    19022410153984, 12360915877888, 206158430208, 1322849927168, 7095285972992, 7687991459840,
    722422089121792, 137438953472, 1005022347264, 37417755082752, 4810363371520, 873271004233728,
    233594681294848, 6133213298688, 240518168576, 68719476736, 6150393167872, 68719476736,
    1992864825344, 36352603193344, 240518168576, 936307165495296, 51539607552, 20401094656,
    137438953472, 137438953472, 103079215104, 790207410470912, 463856467968, 23622320128,
    68719476736, 1155021932593152, 4660039516160, 36146444763136, 1074858515496960, 137438953472,
    34359738368, 8796093022208, 57982058496, 631465419210752, 9105330667520, 206158430208,
    71601399791616, 68719476736, 272249386958848, 549755813888, 34359738368, 261546328457216,
    40475771797504, 103079215104, 206158430208, 221278862573568, 377957122048, 154618822656,
    240518168576, 68719476736, 103079215104, 205643034132480, 206158430208, 8778913153024,
    103079215104, 1168231104512, 309237645312, 68719476736
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
noncomputable def floor : ℝ := 2206874107109 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive5
