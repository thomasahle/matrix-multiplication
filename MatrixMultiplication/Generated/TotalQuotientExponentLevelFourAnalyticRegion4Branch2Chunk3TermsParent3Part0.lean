import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3

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
def constantNumerator : ℤ := 389358304606374844291707043840
def positiveArguments : Array ℕ := #[
    9, 12582907, 12582917, 5686317, 80319401, 22764451,
    397155, 122651811, 122651907, 1588641, 113583, 3603489,
    42894295, 900877, 116773
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 237684393095463355387727577088, 237684581990122670173536124928, 429645964988349957801731162112, 1517190588826266658586318864384, 430008321613313511418268483584,
    30008183368065503117526958080, 1158413602659324924774592806912, 1158414509353689635746473836544, 30008580046850064167724908544, 1072761104447565824614465536, 34033991349978909922912370688,
    405125162028646016683228528640, 34034170799905258969430491136, 1102889802608274161077846016
  ]
def positiveScales : Array ℕ := #[
    3, 23, 23, 22, 26, 24,
    18, 26, 26, 20, 16, 21,
    25, 19, 16
  ]
def negativeArguments : Array ℕ := #[
    476401414807, 15114122033541, 179911642212915, 944637607827, 489781260417, 9645445982655,
    23247288709929, 185978455736589, 9645571613079, 9645445982655, 34005380371495, 4827207704845,
    476401414807, 476401847657, 476401847657, 15114134619771, 179911783978445, 944638394477,
    489781661567, 34005380371495, 2565487928613, 1313530845513777, 4250729225013, 23247288709929,
    2565487928613, 23266842945591, 15114122033541, 15114134619771, 4827207704845, 23266842945591,
    372269779563957, 9654540993729, 185978455736589, 1313530845513777, 372269779563957, 179911642212915,
    179911783978445, 9645571613079, 4250729225013, 9654540993729, 944637607827, 944638394477,
    489781260417, 489781661567, 3, 15, 15, 3
  ]
def negativeCoefficients : Array ℕ := #[
    268190154275447786946166784, 8508494294785931355768225792, 101281250603712249047002644480, 8508539157219667871356944384, 275722337738381632789807104, 2714951683331706601529671680,
    104696480771410583074356854784, 104696562994280313073610784768, 2714987045152376151368269824, 2714951683331706601529671680, 9571663648103553802405150720, 2717476352597491154828656640,
    268190154275447786946166784, 268190397948335125361065984, 268190397948335125361065984, 8508501380203523605687959552, 101281330410610759294611619840, 8508546242732961613358301184,
    275722563565755447749115904, 9571663648103553802405150720, 369725775338400398174412865536, 369726064149718665293790707712, 9571791276910712022550708224, 104696480771410583074356854784,
    369725775338400398174412865536, 104784545219851481138526683136, 8508494294785931355768225792, 8508501380203523605687959552, 2717476352597491154828656640, 104784545219851481138526683136,
    104784627532845839505835425792, 2717511701361943909943476224, 104696562994280313073610784768, 369726064149718665293790707712, 104784627532845839505835425792, 101281250603712249047002644480,
    101281330410610759294611619840, 2714987045152376151368269824, 9571791276910712022550708224, 2717511701361943909943476224, 8508539157219667871356944384, 8508546242732961613358301184,
    275722337738381632789807104, 275722563565755447749115904, 475368975085586025561263702016, 2376844875427930127806318510080, 2376844875427930127806318510080, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    38, 43, 47, 39, 38, 43,
    44, 47, 43, 43, 44, 42,
    38, 38, 38, 43, 47, 39,
    38, 44, 41, 50, 41, 44,
    41, 44, 43, 43, 42, 44,
    48, 43, 47, 50, 48, 47,
    47, 43, 41, 43, 39, 39,
    38, 38, 1, 3, 3, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 23584961927445308, 23584963073996313, 22439063097741655, 26259245174317553, 24440279331162408,
    18599342640719966, 26869993294928984, 26869994424130976, 20599361711608923, 16793387396823700, 21780963010683143,
    25354282444278480, 19780970617514605, 16833347210314610
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38793386742019267, 43780962410446781, 47354281875876170, 39780970017273370, 38833346620836798, 43132985085278292,
    44402127700602391, 47402128833615449, 43133003876032983, 43132985085278292, 44950828273444970, 42134326042974472,
    38793386742019267, 38793388052826188, 38793388052826188, 43780963611845326, 47354283012680571, 39780971218681807,
    38833347802459983, 44950828273444970, 41222370375882556, 50222371502843460, 41950847510252613, 44402127700602391,
    41222370375882556, 44403340699726562, 43780962410446781, 43780963611845326, 42134326042974472, 44403340699726562,
    48403341833028251, 43134344809340348, 47402128833615449, 50222371502843460, 48403341833028251, 47354281875876170,
    47354283012680571, 43133003876032983, 41950847510252613, 43134344809340348, 39780970017273370, 39780971218681807,
    38833346620836798, 38833347802459983, 1584962500724866, 3906890600547867, 3906890600547867, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 935254013 / 500000000000
noncomputable def negativeCeiling : ℝ := 1818545733 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 268190154275447786946166784, coefficient := (-268190154275447786946166784) }, { argument := 8508494294785931355768225792, coefficient := (-8508494294785931355768225792) }, { argument := 101281250603712249047002644480, coefficient := (-101281250603712249047002644480) }, { argument := 8508539157219667871356944384, coefficient := (-8508539157219667871356944384) }, { argument := 275722337738381632789807104, coefficient := (-275722337738381632789807104) }, { argument := 2714951683331706601529671680, coefficient := (-2714951683331706601529671680) }, { argument := 104696480771410583074356854784, coefficient := (-104696480771410583074356854784) }, { argument := 104696562994280313073610784768, coefficient := (-104696562994280313073610784768) }, { argument := 2714987045152376151368269824, coefficient := (-2714987045152376151368269824) }, { argument := 2714951683331706601529671680, coefficient := (-2714951683331706601529671680) }, { argument := 9571663648103553802405150720, coefficient := (-9571663648103553802405150720) }, { argument := 2717476352597491154828656640, coefficient := (-2717476352597491154828656640) }, { argument := 268190154275447786946166784, coefficient := (-268190154275447786946166784) }, { argument := 268190397948335125361065984, coefficient := (-268190397948335125361065984) }, { argument := 268190397948335125361065984, coefficient := (-268190397948335125361065984) }, { argument := 8508501380203523605687959552, coefficient := (-8508501380203523605687959552) }, { argument := 101281330410610759294611619840, coefficient := (-101281330410610759294611619840) }, { argument := 8508546242732961613358301184, coefficient := (-8508546242732961613358301184) }, { argument := 275722563565755447749115904, coefficient := (-275722563565755447749115904) }, { argument := 9571663648103553802405150720, coefficient := (-9571663648103553802405150720) }, { argument := 369725775338400398174412865536, coefficient := (-369725775338400398174412865536) }, { argument := 369726064149718665293790707712, coefficient := (-369726064149718665293790707712) }, { argument := 9571791276910712022550708224, coefficient := (-9571791276910712022550708224) }, { argument := 104696480771410583074356854784, coefficient := (-104696480771410583074356854784) }, { argument := 369725775338400398174412865536, coefficient := (-369725775338400398174412865536) }, { argument := 104784545219851481138526683136, coefficient := (-104784545219851481138526683136) }, { argument := 8508494294785931355768225792, coefficient := (-8508494294785931355768225792) }, { argument := 8508501380203523605687959552, coefficient := (-8508501380203523605687959552) }, { argument := 2717476352597491154828656640, coefficient := (-2717476352597491154828656640) }, { argument := 104784545219851481138526683136, coefficient := (-104784545219851481138526683136) }, { argument := 104784627532845839505835425792, coefficient := (-104784627532845839505835425792) }, { argument := 2717511701361943909943476224, coefficient := (-2717511701361943909943476224) }, { argument := 104696562994280313073610784768, coefficient := (-104696562994280313073610784768) }, { argument := 369726064149718665293790707712, coefficient := (-369726064149718665293790707712) }, { argument := 104784627532845839505835425792, coefficient := (-104784627532845839505835425792) }, { argument := 101281250603712249047002644480, coefficient := (-101281250603712249047002644480) }, { argument := 101281330410610759294611619840, coefficient := (-101281330410610759294611619840) }, { argument := 2714987045152376151368269824, coefficient := (-2714987045152376151368269824) }, { argument := 9571791276910712022550708224, coefficient := (-9571791276910712022550708224) }, { argument := 2717511701361943909943476224, coefficient := (-2717511701361943909943476224) }, { argument := 8508539157219667871356944384, coefficient := (-8508539157219667871356944384) }, { argument := 8508546242732961613358301184, coefficient := (-8508546242732961613358301184) }, { argument := 275722337738381632789807104, coefficient := (-275722337738381632789807104) }, { argument := 275722563565755447749115904, coefficient := (-275722563565755447749115904) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 237684393095463355387727577088, coefficient := 237684393095463355387727577088 }, { argument := 237684581990122670173536124928, coefficient := 237684581990122670173536124928 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 429645964988349957801731162112, coefficient := 429645964988349957801731162112 }, { argument := 1517190588826266658586318864384, coefficient := 1517190588826266658586318864384 }, { argument := 430008321613313511418268483584, coefficient := 430008321613313511418268483584 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 30008183368065503117526958080, coefficient := 30008183368065503117526958080 }, { argument := 1158413602659324924774592806912, coefficient := 1158413602659324924774592806912 }, { argument := 1158414509353689635746473836544, coefficient := 1158414509353689635746473836544 }, { argument := 30008580046850064167724908544, coefficient := 30008580046850064167724908544 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 1072761104447565824614465536, coefficient := 1072761104447565824614465536 }, { argument := 34033991349978909922912370688, coefficient := 34033991349978909922912370688 }, { argument := 405125162028646016683228528640, coefficient := 405125162028646016683228528640 }, { argument := 34034170799905258969430491136, coefficient := 34034170799905258969430491136 }, { argument := 1102889802608274161077846016, coefficient := 1102889802608274161077846016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3
