import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive2

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    547, 549, 551, 553, 555, 557,
    559, 561, 563, 565, 567, 569,
    571, 575, 577, 585, 587, 589,
    595, 597, 603, 605, 611, 613,
    617, 619, 621, 623, 625, 627,
    629, 631, 633, 637, 639, 641,
    643, 645, 649, 657, 667, 669,
    671, 673, 675, 677, 679, 681,
    685, 687, 689, 701, 705, 709,
    711, 715, 719, 723, 725, 727,
    731, 733, 741, 745
  ]

def coefficients : Array ℕ := #[
    671011330588672, 29978871726080, 1642824990720, 1292337405755392, 465074091196416, 2567738144849920,
    541638325698560, 384298641260544, 20426864459776, 1649267441664, 191353677938688, 324974405484544,
    249709398589440, 103079215104, 196550588366848, 20100446945280, 880043093917696, 384416752861184,
    1021618100895744, 687194767360, 277372209201152, 18073222381568, 57982058496, 283575215718400,
    35046933135360, 372940600246272, 91860760526848, 1821066133504, 68719476736, 505174053355520,
    274877906944, 27260157427712, 206158430208, 128849018880, 34359738368, 171798691840,
    154618822656, 173946175488, 3143916060672, 1202590842880, 25769803776, 463856467968,
    95485712924672, 412316860416, 3367254360064, 163208757248, 171798691840, 755914244096,
    34359738368, 206020991254528, 132422431670272, 68719476736, 137438953472, 257654014345216,
    274877906944, 3813930958848, 934541933936640, 415855913467904, 7112465842176, 367219703808,
    171798691840, 137438953472, 5746666242048, 17381732646912
  ]

def scales : Array ℕ := #[
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9,
    9, 9, 9, 9
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
noncomputable def floor : ℝ := 331051124657 / 100000000000

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

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive2
