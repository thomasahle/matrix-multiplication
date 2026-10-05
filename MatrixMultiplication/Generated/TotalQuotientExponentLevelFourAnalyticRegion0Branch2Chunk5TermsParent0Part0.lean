import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5

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
def constantNumerator : ℤ := 3091864253801393952746945642496
def positiveArguments : Array ℕ := #[
    11, 5242711, 5243049, 18046403, 16140789, 18053737,
    1069779, 10218419, 40885151, 528737
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 396128043292352008447061917696, 396153581850291367488377585664, 340886914654232855973516541952, 1219563535690736926386032738304, 341025449997374319885505527808,
    10103776987355612374124986368, 386040955148146857399122132992, 386149333458928715756776456192, 9987559548212190405415927808
  ]
def positiveScales : Array ℕ := #[
    3, 22, 22, 24, 23, 24,
    20, 23, 25, 19
  ]
def negativeArguments : Array ℕ := #[
    1121704966041, 171431110489175, 171479237766615, 2217605685175, 54277624061319, 194191001182833,
    6787471988737, 1121704966041, 1121784203367, 1121784203367, 171442134993833, 171490266993193,
    2217761742921, 194191001182833, 347364635785811, 194269741099241, 171431110489175, 171442134993833,
    6787471988737, 194269741099241, 54321928247055, 171479237766615, 171490266993193, 2217605685175,
    2217761742921, 5, 3, 5
  ]
def negativeCoefficients : Array ℕ := #[
    2525855033540941234902663168, 96507135664844857281190297600, 96534228913437999841023098880, 2496802034352205866414899200, 30555585937139014516529430528, 109319815070713780847190736896,
    30568056319263632623038103552, 2525855033540941234902663168, 2526033460136864952159830016, 2526033460136864952159830016, 96513341909228571418370768896, 96540437816026358037365129216,
    2496977739753889336293064704, 109319815070713780847190736896, 391097811071666619898149208064, 109364141702988062447676424192, 96507135664844857281190297600, 96513341909228571418370768896,
    30568056319263632623038103552, 109364141702988062447676424192, 30580526976435464872038236160, 96534228913437999841023098880, 96540437816026358037365129216, 2496802034352205866414899200,
    2496977739753889336293064704, 792281625142643375935439503360, 1901475900342344102245054808064, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    40, 47, 47, 41, 45, 47,
    42, 40, 40, 40, 47, 47,
    41, 47, 48, 47, 47, 47,
    42, 47, 45, 47, 47, 41,
    41, 2, 1, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22321881590029041, 22321974598246660, 24105207972725675, 23944207766318506, 24105794160234945,
    20028881357973912, 23284668663099425, 25285073632845454, 19012190761716976
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40028830402828857, 47284622274954208, 47285027237856630, 41012139999812622, 45625422803419902, 47464469676195181,
    42626011477721369, 40028830402828857, 40028932311319327, 40028932311319327, 47284715049753137, 47285120026342333,
    41012241521835313, 47464469676195181, 48303444213232931, 47465054536780117, 47284622274954208, 47284715049753137,
    42626011477721369, 47465054536780117, 45626599924895242, 47285027237856630, 47285120026342333, 41012139999812622,
    41012241521835313, 2321928094887363, 1584962500724866, 2321928094887363
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
noncomputable def positiveFloor : ℝ := 532635999 / 500000000000
noncomputable def negativeCeiling : ℝ := 214419327 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2525855033540941234902663168, coefficient := (-2525855033540941234902663168) }, { argument := 96507135664844857281190297600, coefficient := (-96507135664844857281190297600) }, { argument := 96534228913437999841023098880, coefficient := (-96534228913437999841023098880) }, { argument := 2496802034352205866414899200, coefficient := (-2496802034352205866414899200) }, { argument := 30555585937139014516529430528, coefficient := (-30555585937139014516529430528) }, { argument := 109319815070713780847190736896, coefficient := (-109319815070713780847190736896) }, { argument := 30568056319263632623038103552, coefficient := (-30568056319263632623038103552) }, { argument := 2525855033540941234902663168, coefficient := (-2525855033540941234902663168) }, { argument := 2526033460136864952159830016, coefficient := (-2526033460136864952159830016) }, { argument := 2526033460136864952159830016, coefficient := (-2526033460136864952159830016) }, { argument := 96513341909228571418370768896, coefficient := (-96513341909228571418370768896) }, { argument := 96540437816026358037365129216, coefficient := (-96540437816026358037365129216) }, { argument := 2496977739753889336293064704, coefficient := (-2496977739753889336293064704) }, { argument := 109319815070713780847190736896, coefficient := (-109319815070713780847190736896) }, { argument := 391097811071666619898149208064, coefficient := (-391097811071666619898149208064) }, { argument := 109364141702988062447676424192, coefficient := (-109364141702988062447676424192) }, { argument := 96507135664844857281190297600, coefficient := (-96507135664844857281190297600) }, { argument := 96513341909228571418370768896, coefficient := (-96513341909228571418370768896) }, { argument := 30568056319263632623038103552, coefficient := (-30568056319263632623038103552) }, { argument := 109364141702988062447676424192, coefficient := (-109364141702988062447676424192) }, { argument := 30580526976435464872038236160, coefficient := (-30580526976435464872038236160) }, { argument := 96534228913437999841023098880, coefficient := (-96534228913437999841023098880) }, { argument := 96540437816026358037365129216, coefficient := (-96540437816026358037365129216) }, { argument := 2496802034352205866414899200, coefficient := (-2496802034352205866414899200) }, { argument := 2496977739753889336293064704, coefficient := (-2496977739753889336293064704) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 396128043292352008447061917696, coefficient := 396128043292352008447061917696 }, { argument := 396153581850291367488377585664, coefficient := 396153581850291367488377585664 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 340886914654232855973516541952, coefficient := 340886914654232855973516541952 }, { argument := 1219563535690736926386032738304, coefficient := 1219563535690736926386032738304 }, { argument := 341025449997374319885505527808, coefficient := 341025449997374319885505527808 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 10103776987355612374124986368, coefficient := 10103776987355612374124986368 }, { argument := 386040955148146857399122132992, coefficient := 386040955148146857399122132992 }, { argument := 386149333458928715756776456192, coefficient := 386149333458928715756776456192 }, { argument := 9987559548212190405415927808, coefficient := 9987559548212190405415927808 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5
