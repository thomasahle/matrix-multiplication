import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 8, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8

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
def constantNumerator : ℤ := (-56848334313427183970715267235840)
def positiveArguments : Array ℕ := #[
    41, 7, 24645993, 2545, 24642199, 1285,
    19465259, 285, 93, 272297647, 939, 77861029,
    1881, 843, 285, 93
  ]
def positiveCoefficients : Array ℕ := #[
    6496709326169675682670603927552, 4436777100798802905238461218816, 1862198580483838333587761922048, 196909837498830799976141946880, 1861911913948862214644709720064, 198844118810214206655671828480,
    735376693455813658581623898112, 88203227799083344586562600960, 3597763239173136423925579776, 2571778563114140398828465946624, 72651606055560754883142352896, 735376627342682898406590906368,
    72767662934243759283914145792, 65223965819848473233747607552, 88203227799083344586562600960, 3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    5, 2, 24, 11, 24, 10,
    24, 8, 6, 28, 9, 26,
    10, 9, 8, 6
  ]
def negativeArguments : Array ℕ := #[
    19465259, 285, 93, 272297647, 939, 77861029,
    1881, 843, 285, 93, 11014505, 2545,
    21509, 1285, 19465259, 2545, 2545, 285,
    93, 21509, 2545, 11010711, 1285, 272297647,
    939, 77861029, 1285, 1285, 1881, 843,
    285, 93, 7, 13, 7
  ]
def negativeCoefficients : Array ℕ := #[
    367688346727906829290811949056, 44101613899541672293281300480, 1798881619586568211962789888, 1285889281557070199414232973312, 36325803027780377441571176448, 367688313671341449203295453184,
    36383831467121879641957072896, 32611982909924236616873803776, 44101613899541672293281300480, 1798881619586568211962789888, 416116233899200972435845283840, 49227459374707699994035486720,
    416044567265456942700082233344, 49711029702553551663917957120, 367688346727906829290811949056, 49227459374707699994035486720, 49227459374707699994035486720, 44101613899541672293281300480,
    1798881619586568211962789888, 416044567265456942700082233344, 49227459374707699994035486720, 415972900631712912964319182848, 49711029702553551663917957120, 1285889281557070199414232973312,
    36325803027780377441571176448, 367688313671341449203295453184, 49711029702553551663917957120, 49711029702553551663917957120, 36383831467121879641957072896, 32611982909924236616873803776,
    44101613899541672293281300480, 1798881619586568211962789888, 4436777100798802905238461218816, 4119864450741745554864285417472, 4436777100798802905238461218816
  ]
def negativeScales : Array ℕ := #[
    24, 8, 6, 28, 9, 26,
    10, 9, 8, 6, 23, 11,
    14, 10, 24, 11, 11, 8,
    6, 14, 11, 23, 10, 28,
    9, 26, 10, 10, 10, 9,
    8, 6, 2, 3, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5357552004618083, 2807354922011143, 24554849773332378, 11313449940963057, 24554627668005572, 10327552644081240,
    24214398205173623, 8154818109052103, 6539158811107971, 28020609274803787, 9874981347482478, 26214398075469906,
    10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24214398205173624, 8154818109052105, 6539158811108986, 28020609274803788, 9874981350423323, 26214398075469908,
    10877284136413052, 9719388821055554, 8154818109052105, 6539158811108986, 23392901324925158, 11313449940963058,
    14392652831852159, 10327552644081241, 24214398205173624, 11313449940963058, 11313449940963058, 8154818109052105,
    6539158811108986, 14392652831852159, 11313449940963058, 23392404295970775, 10327552644081241, 28020609274803788,
    9874981350423323, 26214398075469908, 10327552644081241, 10327552644081241, 10877284136413052, 9719388821055554,
    8154818109052105, 6539158811108986, 2807354922807594, 3700439718214233, 2807354922807594
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 35
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
noncomputable def positiveFloor : ℝ := 615727967 / 200000000000
noncomputable def negativeCeiling : ℝ := 567710081 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 367688346727906829290811949056, coefficient := (-367688346727906829290811949056) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 1285889281557070199414232973312, coefficient := (-1285889281557070199414232973312) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 367688313671341449203295453184, coefficient := (-367688313671341449203295453184) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 416116233899200972435845283840, coefficient := (-416116233899200972435845283840) }, { argument := 49227459374707699994035486720, coefficient := (-49227459374707699994035486720) }, { argument := 416044567265456942700082233344, coefficient := (-416044567265456942700082233344) }, { argument := 49711029702553551663917957120, coefficient := (-49711029702553551663917957120) }, { argument := 367688346727906829290811949056, coefficient := (-367688346727906829290811949056) }, { argument := 49227459374707699994035486720, coefficient := (-49227459374707699994035486720) }, { argument := 49227459374707699994035486720, coefficient := (-49227459374707699994035486720) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 416044567265456942700082233344, coefficient := (-416044567265456942700082233344) }, { argument := 49227459374707699994035486720, coefficient := (-49227459374707699994035486720) }, { argument := 415972900631712912964319182848, coefficient := (-415972900631712912964319182848) }, { argument := 49711029702553551663917957120, coefficient := (-49711029702553551663917957120) }, { argument := 1285889281557070199414232973312, coefficient := (-1285889281557070199414232973312) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 367688313671341449203295453184, coefficient := (-367688313671341449203295453184) }, { argument := 49711029702553551663917957120, coefficient := (-49711029702553551663917957120) }, { argument := 49711029702553551663917957120, coefficient := (-49711029702553551663917957120) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 6496709326169675682670603927552, coefficient := 6496709326169675682670603927552 }, { argument := 4436777100798802905238461218816, coefficient := 4436777100798802905238461218816 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 1862198580483838333587761922048, coefficient := 1862198580483838333587761922048 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 1861911913948862214644709720064, coefficient := 1861911913948862214644709720064 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 4119864450741745554864285417472, coefficient := (-4119864450741745554864285417472) }, { argument := 735376693455813658581623898112, coefficient := 735376693455813658581623898112 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 2571778563114140398828465946624, coefficient := 2571778563114140398828465946624 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 735376627342682898406590906368, coefficient := 735376627342682898406590906368 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
