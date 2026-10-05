import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive4

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1013, 1021, 1023, 1025, 1027, 1029,
    1031, 1033, 1037, 1039, 1041, 1043,
    1049, 1051, 1053, 1057, 1059, 1063,
    1071, 1073, 1079, 1081, 1083, 1085,
    1087, 1091, 1093, 1095, 1097, 1099,
    1107, 1109, 1115, 1117, 1119, 1121,
    1123, 1127, 1129, 1131, 1133, 1135,
    1139, 1141, 1147, 1149, 1151, 1155,
    1157, 1163, 1169, 1171, 1175, 1177,
    1179, 1181, 1183, 1185, 1187, 1189,
    1191, 1193, 1195, 1197
  ]

def coefficients : Array ℕ := #[
    171798691840, 34823594835968, 24326694764544, 95331094102016, 130146099003392, 228022498099200,
    149048250073088, 443848362819584, 326417514496000, 78370268250112, 149095494713344, 326726752141312,
    9371618639872, 30672508944384, 214748364800, 387534899118080, 646822074777600, 18569291104256,
    245906741919744, 100021198389248, 3524646657851392, 1058241287028736, 200799384764416, 137438953472,
    2611340115968, 268277079080960, 51539607552, 21401822035968, 12317966204928, 7204807639040,
    176093659136, 3620657430528, 360777252864, 42305427865600, 2857998477164544, 5935644803072,
    2422389472231424, 91502130757632, 157917357539328, 41253160878080, 495814245875712, 42571715837952,
    944165881905152, 68719476736, 103579578793984, 658377684287488, 11716670783488, 8090161996890112,
    326417514496, 6575594930176, 5325759447040, 2951462871105536, 161684043857920, 24292335026176,
    374430953897984, 1656783634432, 63844688855040, 154618822656, 107099304493056, 23910082936832,
    103079215104, 7344594329010176, 2250562863104, 103079215104
  ]

def scales : Array ℕ := #[
    9, 9, 9, 10, 10, 10,
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
noncomputable def floor : ℝ := 10017700734599 / 1000000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive4
