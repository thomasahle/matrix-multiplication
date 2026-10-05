import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    17, 115, 129, 275, 557, 833,
    921, 1023, 1147, 3703, 4607
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 16241773315424189206676509818880, 31849721330734263712604668035072, 114563922995626232160264552185856, 115514660945797404211387079589888, 143086061500761393693940374306816,
    16321001477938453544270053769216, 135559386061906281622553699024896, 128349623273108226901541199544320, 586763771580641684217786496188416, 128824992248193812927102463246336
  ]
def positiveScales : Array ℕ := #[
    4, 6, 7, 8, 9, 9,
    9, 9, 10, 11, 12
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 13, 27, 49,
    57, 81, 201, 245, 247, 397,
    409, 497, 499, 723, 729, 827,
    9521211903
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 6338253001141147007483516026880, 6100568513598353994702884175872, 1029966112685436388716071354368, 4278320775770274230051373318144, 15528719852795810168334614265856,
    4516005263313067242832005169152, 6417481163655411345077059977216, 31849721330734263712604668035072, 19410899815994762710418267832320, 19569356141023291385605355732992, 31453580518162942024636948283392,
    64808636936668228151518951374848, 39376396769589375783991343316992, 39534853094617904459178431217664, 114563922995626232160264552185856, 115514660945797404211387079589888, 65521690399296607189860846927872,
    293381885790320842108893248094208
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 3, 4, 5,
    5, 6, 7, 7, 7, 8,
    8, 8, 8, 9, 9, 9,
    33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 6845490050846035, 7011227255423254, 8103287808412021, 9121533517340031, 9702172685360817,
    9847057345989998, 9998590428318153, 10163649676015824, 11854478834054907, 12169611882604210
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 3700439718214233, 4754887502413606, 5614709844123661,
    5832890015409720, 6339850002884626, 7651051691200812, 7936637947306280, 7948367241724988, 8632995197156697,
    8675957032982435, 8957102053308650, 8962896018276254, 9497851836951370, 9509775004327312, 9691743519230811,
    33148498071970202
  ]

abbrev PositiveTerm := Fin 11
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 18116788023 / 100000000000
noncomputable def negativeCeiling : ℝ := 89391347889 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 5, coefficient := (-6338253001141147007483516026880) }, { argument := 7, coefficient := (-6100568513598353994702884175872) }, { argument := 13, coefficient := (-1029966112685436388716071354368) }, { argument := 17, coefficient := 475368975085586025561263702016 }, { argument := 27, coefficient := (-4278320775770274230051373318144) }, { argument := 49, coefficient := (-15528719852795810168334614265856) }, { argument := 57, coefficient := (-4516005263313067242832005169152) }, { argument := 81, coefficient := (-6417481163655411345077059977216) }, { argument := 115, coefficient := 16241773315424189206676509818880 }, { argument := 129, coefficient := 31849721330734263712604668035072 }, { argument := 201, coefficient := (-31849721330734263712604668035072) }, { argument := 245, coefficient := (-19410899815994762710418267832320) }, { argument := 247, coefficient := (-19569356141023291385605355732992) }, { argument := 275, coefficient := 114563922995626232160264552185856 }, { argument := 397, coefficient := (-31453580518162942024636948283392) }, { argument := 409, coefficient := (-64808636936668228151518951374848) }, { argument := 497, coefficient := (-39376396769589375783991343316992) }, { argument := 499, coefficient := (-39534853094617904459178431217664) }, { argument := 557, coefficient := 115514660945797404211387079589888 }, { argument := 723, coefficient := (-114563922995626232160264552185856) }, { argument := 729, coefficient := (-115514660945797404211387079589888) }, { argument := 827, coefficient := (-65521690399296607189860846927872) }, { argument := 833, coefficient := 143086061500761393693940374306816 }, { argument := 921, coefficient := 16321001477938453544270053769216 }, { argument := 1023, coefficient := 135559386061906281622553699024896 }, { argument := 1147, coefficient := 128349623273108226901541199544320 }, { argument := 3703, coefficient := 586763771580641684217786496188416 }, { argument := 4607, coefficient := 128824992248193812927102463246336 }, { argument := 9521211903, coefficient := (-293381885790320842108893248094208) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7
