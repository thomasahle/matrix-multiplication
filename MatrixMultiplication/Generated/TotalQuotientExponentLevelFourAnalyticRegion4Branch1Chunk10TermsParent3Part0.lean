import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 475368975085586025561263702016
def positiveArguments : Array ℕ := #[
    1, 3100025, 10577173, 1550009, 203781, 2046205,
    8186411, 50551, 18885, 1283667, 14134327, 1283687,
    37765
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 29278908312115943807175884800, 99898574517427547747769122816, 29278842198985183632142893056, 3849314256982636685168738304, 154606878545284518151853178880,
    154636931685581500573993140224, 3819525569208694963160743936, 356727564115972999442595840, 12123892031931657725059006464, 133494944165438927648728285184, 12124080926590972510867554304,
    356680340451144302990458880
  ]
def positiveScales : Array ℕ := #[
    0, 21, 23, 20, 17, 20,
    22, 15, 14, 20, 23, 20,
    15
  ]
def negativeArguments : Array ℕ := #[
    58543972125, 3979399791675, 43816767058175, 3979461792175, 117072444125, 41526695961,
    416977701105, 1668235019991, 10301333331, 58543972125, 199749912105, 29271919965,
    199749912105, 13577567933391, 149501221917571, 13577779476851, 399446938345, 416977701105,
    4186954902025, 16751075120255, 103437708955, 3979399791675, 13577567933391, 1989695403003,
    29271919965, 1989695403003, 21908334058943, 1989726403183, 58536089885, 1668235019991,
    16751075120255, 67017325060921, 413831262461, 43816767058175, 149501221917571, 21908334058943,
    10301333331, 103437708955, 413831262461, 2555403601, 3979461792175, 13577779476851,
    1989726403183, 117072444125, 399446938345, 58536089885, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    32957326380867338108928000, 1120101463684109963152588800, 12333323487236047139294412800, 1120118915273403512179916800, 32952963483543950852096000, 23377451556985935161720832,
    938950309659142029091799040, 939132826799734943165448192, 23196540475455435165401088, 32957326380867338108928000, 112449203715420916033781760, 32957251961698245578588160,
    112449203715420916033781760, 3821745617838581440887914496, 42080852957462911566349336576, 3821805162029058232477024256, 112434317667801718136504320, 938950309659142029091799040,
    37712737073153723176111308800, 37720067834817802236319498240, 931684055011591634403983360, 1120101463684109963152588800, 3821745617838581440887914496, 1120098934443137458488999936,
    32957251961698245578588160, 1120098934443137458488999936, 12333295638020505118720393216, 1120116385993024510776836096, 32952889074226482506629120, 939132826799734943165448192,
    37720067834817802236319498240, 37727400021466402342779748352, 931865159706810764731875328, 12333323487236047139294412800, 42080852957462911566349336576, 12333295638020505118720393216,
    23196540475455435165401088, 931684055011591634403983360, 931865159706810764731875328, 23017029410489647279112192, 1120118915273403512179916800, 3821805162029058232477024256,
    1120116385993024510776836096, 32952963483543950852096000, 112434317667801718136504320, 32952889074226482506629120, 158456325028528675187087900672, 316912650057057350374175801344,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 41, 45, 41, 36, 35,
    38, 40, 33, 35, 37, 34,
    37, 43, 47, 43, 38, 38,
    41, 43, 36, 41, 43, 40,
    34, 40, 44, 40, 35, 40,
    43, 45, 38, 45, 47, 44,
    33, 36, 38, 31, 41, 43,
    40, 36, 38, 35, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 21563848419414074, 23334450748764632, 20563845161738188, 17636660019150534, 20964519257901833,
    22964799667821649, 15625452011355991, 14204953163327534, 20291839566366545, 23752699855687199, 20291862043906315,
    15204762166432983
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35768801583079056, 41855687987710757, 45316548275116194, 41855710465251348, 36768610586183136, 35273320038302950,
    38601179277879414, 40601459687803097, 33262112030508168, 35768801583079056, 37539403912093130, 34768798325403147,
    37539403912093130, 43626290315142697, 47087150604466627, 43626312792682473, 38539212915198572, 38601179277879414,
    41929038524728716, 43929318934687792, 36589971270083064, 41855687987710757, 43626290315142697, 40855684730034752,
    34768798325403147, 40855684730034752, 44316545017440308, 40855707207575343, 35768607328507226, 40601459687803097,
    43929318934687792, 45929599344647027, 38590251680006735, 45316548275116194, 47087150604466627, 44316545017440308,
    33262112030508168, 36589971270083064, 38590251680006735, 31250904022713386, 41855710465251348, 43626312792682473,
    40855707207575343, 36768610586183136, 38539212915198572, 35768607328507226, 0, 0,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 170420219 / 1000000000000
noncomputable def negativeCeiling : ℝ := 8521011 / 50000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 32957326380867338108928000, coefficient := (-32957326380867338108928000) }, { argument := 1120101463684109963152588800, coefficient := (-1120101463684109963152588800) }, { argument := 12333323487236047139294412800, coefficient := (-12333323487236047139294412800) }, { argument := 1120118915273403512179916800, coefficient := (-1120118915273403512179916800) }, { argument := 32952963483543950852096000, coefficient := (-32952963483543950852096000) }, { argument := 23377451556985935161720832, coefficient := (-23377451556985935161720832) }, { argument := 938950309659142029091799040, coefficient := (-938950309659142029091799040) }, { argument := 939132826799734943165448192, coefficient := (-939132826799734943165448192) }, { argument := 23196540475455435165401088, coefficient := (-23196540475455435165401088) }, { argument := 32957326380867338108928000, coefficient := (-32957326380867338108928000) }, { argument := 112449203715420916033781760, coefficient := (-112449203715420916033781760) }, { argument := 32957251961698245578588160, coefficient := (-32957251961698245578588160) }, { argument := 112449203715420916033781760, coefficient := (-112449203715420916033781760) }, { argument := 3821745617838581440887914496, coefficient := (-3821745617838581440887914496) }, { argument := 42080852957462911566349336576, coefficient := (-42080852957462911566349336576) }, { argument := 3821805162029058232477024256, coefficient := (-3821805162029058232477024256) }, { argument := 112434317667801718136504320, coefficient := (-112434317667801718136504320) }, { argument := 938950309659142029091799040, coefficient := (-938950309659142029091799040) }, { argument := 37712737073153723176111308800, coefficient := (-37712737073153723176111308800) }, { argument := 37720067834817802236319498240, coefficient := (-37720067834817802236319498240) }, { argument := 931684055011591634403983360, coefficient := (-931684055011591634403983360) }, { argument := 1120101463684109963152588800, coefficient := (-1120101463684109963152588800) }, { argument := 3821745617838581440887914496, coefficient := (-3821745617838581440887914496) }, { argument := 1120098934443137458488999936, coefficient := (-1120098934443137458488999936) }, { argument := 32957251961698245578588160, coefficient := (-32957251961698245578588160) }, { argument := 1120098934443137458488999936, coefficient := (-1120098934443137458488999936) }, { argument := 12333295638020505118720393216, coefficient := (-12333295638020505118720393216) }, { argument := 1120116385993024510776836096, coefficient := (-1120116385993024510776836096) }, { argument := 32952889074226482506629120, coefficient := (-32952889074226482506629120) }, { argument := 939132826799734943165448192, coefficient := (-939132826799734943165448192) }, { argument := 37720067834817802236319498240, coefficient := (-37720067834817802236319498240) }, { argument := 37727400021466402342779748352, coefficient := (-37727400021466402342779748352) }, { argument := 931865159706810764731875328, coefficient := (-931865159706810764731875328) }, { argument := 12333323487236047139294412800, coefficient := (-12333323487236047139294412800) }, { argument := 42080852957462911566349336576, coefficient := (-42080852957462911566349336576) }, { argument := 12333295638020505118720393216, coefficient := (-12333295638020505118720393216) }, { argument := 23196540475455435165401088, coefficient := (-23196540475455435165401088) }, { argument := 931684055011591634403983360, coefficient := (-931684055011591634403983360) }, { argument := 931865159706810764731875328, coefficient := (-931865159706810764731875328) }, { argument := 23017029410489647279112192, coefficient := (-23017029410489647279112192) }, { argument := 1120118915273403512179916800, coefficient := (-1120118915273403512179916800) }, { argument := 3821805162029058232477024256, coefficient := (-3821805162029058232477024256) }, { argument := 1120116385993024510776836096, coefficient := (-1120116385993024510776836096) }, { argument := 32952963483543950852096000, coefficient := (-32952963483543950852096000) }, { argument := 112434317667801718136504320, coefficient := (-112434317667801718136504320) }, { argument := 32952889074226482506629120, coefficient := (-32952889074226482506629120) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 29278908312115943807175884800, coefficient := 29278908312115943807175884800 }, { argument := 99898574517427547747769122816, coefficient := 99898574517427547747769122816 }, { argument := 29278842198985183632142893056, coefficient := 29278842198985183632142893056 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3849314256982636685168738304, coefficient := 3849314256982636685168738304 }, { argument := 154606878545284518151853178880, coefficient := 154606878545284518151853178880 }, { argument := 154636931685581500573993140224, coefficient := 154636931685581500573993140224 }, { argument := 3819525569208694963160743936, coefficient := 3819525569208694963160743936 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 356727564115972999442595840, coefficient := 356727564115972999442595840 }, { argument := 12123892031931657725059006464, coefficient := 12123892031931657725059006464 }, { argument := 133494944165438927648728285184, coefficient := 133494944165438927648728285184 }, { argument := 12124080926590972510867554304, coefficient := 12124080926590972510867554304 }, { argument := 356680340451144302990458880, coefficient := 356680340451144302990458880 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard0


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10
