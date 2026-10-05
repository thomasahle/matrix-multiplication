import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-866627913758308656369845141504)
def positiveArguments : Array ℕ := #[
    1, 16777207, 16777225, 12229127, 42656859, 6111439,
    467059, 2038767, 8155085, 467067
  ]
def positiveCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456240025931983533474054144, 158456410031125366840701747200, 115500838919112431526461046784, 402882642412192742521310281728, 115441818782809526700580274176,
    4411247534245227247727280128, 154044879154891167414261645312, 154045200275812002550136176640, 4411323092108953162050699264
  ]
def positiveScales : Array ℕ := #[
    0, 23, 24, 23, 25, 22,
    18, 20, 22, 18
  ]
def negativeArguments : Array ℕ := #[
    1958986562527, 17102407946511, 17102443598059, 1959020117049, 18696386606527, 16300488980491,
    18687010056725, 1958986562527, 1958988301345, 1958988301345, 17102426386161, 17102462037781,
    1959021855687, 16300488980491, 113730720134525, 32584136235629, 17102407946511, 17102426386161,
    18687010056725, 32584136235629, 18677649645841, 17102443598059, 17102462037781, 1959020117049,
    1959021855687, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1102811394127550757862375424, 38511199027522574642973769728, 38511279307671718633649733632, 1102830283644147732251148288, 10525129969291216177200103424, 36705438049248071921086496768,
    10519851441016927664943923200, 1102811394127550757862375424, 1102812372995062866001264640, 1102812372995062866001264640, 38511240549923009064157052928, 38511320830234282641418354688,
    1102831262410328848774201344, 36705438049248071921086496768, 128049407204606239177283993600, 36686475952242060162284650496, 38511199027522574642973769728, 38511240549923009064157052928,
    10519851441016927664943923200, 36686475952242060162284650496, 10514581998145775523061563392, 38511279307671718633649733632, 38511320830234282641418354688, 1102830283644147732251148288,
    1102831262410328848774201344, 316912650057057350374175801344, 633825300114114700748351602688, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 43, 43, 40, 44, 43,
    44, 40, 40, 40, 43, 43,
    40, 43, 46, 44, 43, 43,
    44, 44, 44, 43, 43, 40,
    40, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 23999999224618300, 24000000773921721, 23543818082163064, 25346274402230479, 22543080686476553,
    18833245280463232, 20959265475289420, 22959268482718643, 18833269991391543
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40833244641518626, 43959264710470418, 43959267717898876, 40833269352524825, 44087824705329665, 43889980480112859,
    44087100988204358, 40833244641518626, 40833245922070061, 40833245922070061, 43959266265969665, 43959269273400954,
    40833270632921768, 43889980480112859, 46692615325893638, 44889234988566684, 43959264710470418, 43959266265969665,
    44087100988204358, 44889234988566684, 44086378154448985, 43959267717898876, 43959269273400954, 40833269352524825,
    40833270632921768, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 90491061 / 250000000000
noncomputable def negativeCeiling : ℝ := 340088499 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1102811394127550757862375424, coefficient := (-1102811394127550757862375424) }, { argument := 38511199027522574642973769728, coefficient := (-38511199027522574642973769728) }, { argument := 38511279307671718633649733632, coefficient := (-38511279307671718633649733632) }, { argument := 1102830283644147732251148288, coefficient := (-1102830283644147732251148288) }, { argument := 10525129969291216177200103424, coefficient := (-10525129969291216177200103424) }, { argument := 36705438049248071921086496768, coefficient := (-36705438049248071921086496768) }, { argument := 10519851441016927664943923200, coefficient := (-10519851441016927664943923200) }, { argument := 1102811394127550757862375424, coefficient := (-1102811394127550757862375424) }, { argument := 1102812372995062866001264640, coefficient := (-1102812372995062866001264640) }, { argument := 1102812372995062866001264640, coefficient := (-1102812372995062866001264640) }, { argument := 38511240549923009064157052928, coefficient := (-38511240549923009064157052928) }, { argument := 38511320830234282641418354688, coefficient := (-38511320830234282641418354688) }, { argument := 1102831262410328848774201344, coefficient := (-1102831262410328848774201344) }, { argument := 36705438049248071921086496768, coefficient := (-36705438049248071921086496768) }, { argument := 128049407204606239177283993600, coefficient := (-128049407204606239177283993600) }, { argument := 36686475952242060162284650496, coefficient := (-36686475952242060162284650496) }, { argument := 38511199027522574642973769728, coefficient := (-38511199027522574642973769728) }, { argument := 38511240549923009064157052928, coefficient := (-38511240549923009064157052928) }, { argument := 10519851441016927664943923200, coefficient := (-10519851441016927664943923200) }, { argument := 36686475952242060162284650496, coefficient := (-36686475952242060162284650496) }, { argument := 10514581998145775523061563392, coefficient := (-10514581998145775523061563392) }, { argument := 38511279307671718633649733632, coefficient := (-38511279307671718633649733632) }, { argument := 38511320830234282641418354688, coefficient := (-38511320830234282641418354688) }, { argument := 1102830283644147732251148288, coefficient := (-1102830283644147732251148288) }, { argument := 1102831262410328848774201344, coefficient := (-1102831262410328848774201344) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 158456240025931983533474054144, coefficient := 158456240025931983533474054144 }, { argument := 158456410031125366840701747200, coefficient := 158456410031125366840701747200 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 115500838919112431526461046784, coefficient := 115500838919112431526461046784 }, { argument := 402882642412192742521310281728, coefficient := 402882642412192742521310281728 }, { argument := 115441818782809526700580274176, coefficient := 115441818782809526700580274176 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 4411247534245227247727280128, coefficient := 4411247534245227247727280128 }, { argument := 154044879154891167414261645312, coefficient := 154044879154891167414261645312 }, { argument := 154045200275812002550136176640, coefficient := 154045200275812002550136176640 }, { argument := 4411323092108953162050699264, coefficient := 4411323092108953162050699264 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8
