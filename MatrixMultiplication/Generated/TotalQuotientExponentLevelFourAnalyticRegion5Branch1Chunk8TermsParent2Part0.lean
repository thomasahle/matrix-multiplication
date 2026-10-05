import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-142175015223138048836236214272)
def positiveArguments : Array ℕ := #[
    1, 1527577, 21336055, 6108069, 467059, 2038767,
    8155085, 467067
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 57710227398420512212816756736, 201513342017326616219809218560, 57689080641310221941549826048, 4411247534245227247727280128, 154044879154891167414261645312,
    154045200275812002550136176640, 4411323092108953162050699264
  ]
def positiveScales : Array ℕ := #[
    0, 20, 24, 22, 18, 20,
    22, 18
  ]
def negativeArguments : Array ℕ := #[
    1427823113491, 6228636400085, 24914597373193, 1427848081971, 1427823113491, 2490374250455,
    1427378113343, 2490374250455, 21749853667295, 21749899092415, 2490416372145, 6228636400085,
    21749853667295, 1556586066323, 1427378113343, 1556586066323, 24905428800507, 1427403119211,
    24914597373193, 21749899092415, 24905428800507, 1427848081971, 2490416372145, 1427403119211,
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    401896477616815563757060096, 14025642285224556819990446080, 14025671430749741658423689216, 401903505619142064237182976, 401896477616815563757060096, 1401956068295277034822696960,
    401771221210521025283883008, 1401956068295277034822696960, 48976316435696288941641564160, 48976418723973041571674193920, 1401979780698700561766154240, 14025642285224556819990446080,
    48976316435696288941641564160, 14020480856524737945498812416, 401771221210521025283883008, 14020480856524737945498812416, 14020509983183218044970205184, 401778259736633955022012416,
    14025671430749741658423689216, 48976418723973041571674193920, 14020509983183218044970205184, 401903505619142064237182976, 1401979780698700561766154240, 401778259736633955022012416,
    316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    40, 42, 44, 40, 40, 41,
    40, 41, 44, 44, 41, 42,
    44, 40, 40, 40, 44, 40,
    44, 44, 44, 40, 41, 40,
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 20542813672587966, 24346790113191498, 22542284929002349, 18833245280463232, 20959265475289420,
    22959268482718643, 18833269991391543
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40376954400160987, 42502053495451720, 44502056493393639, 40376979628487227, 40376954400160987, 41179499703714189,
    40376504694896168, 41179499703714189, 44306070928098088, 44306073941200058, 41179524104962056, 42502053495451720,
    44306070928098088, 40501522486753253, 40376504694896168, 40501522486753253, 44501525483857456, 40376529968876077,
    44502056493393639, 44306073941200058, 44501525483857456, 40376979628487227, 41179524104962056, 40376529968876077,
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 2155201 / 12500000000
noncomputable def negativeCeiling : ℝ := 83445007 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 401896477616815563757060096, coefficient := (-401896477616815563757060096) }, { argument := 14025642285224556819990446080, coefficient := (-14025642285224556819990446080) }, { argument := 14025671430749741658423689216, coefficient := (-14025671430749741658423689216) }, { argument := 401903505619142064237182976, coefficient := (-401903505619142064237182976) }, { argument := 401896477616815563757060096, coefficient := (-401896477616815563757060096) }, { argument := 1401956068295277034822696960, coefficient := (-1401956068295277034822696960) }, { argument := 401771221210521025283883008, coefficient := (-401771221210521025283883008) }, { argument := 1401956068295277034822696960, coefficient := (-1401956068295277034822696960) }, { argument := 48976316435696288941641564160, coefficient := (-48976316435696288941641564160) }, { argument := 48976418723973041571674193920, coefficient := (-48976418723973041571674193920) }, { argument := 1401979780698700561766154240, coefficient := (-1401979780698700561766154240) }, { argument := 14025642285224556819990446080, coefficient := (-14025642285224556819990446080) }, { argument := 48976316435696288941641564160, coefficient := (-48976316435696288941641564160) }, { argument := 14020480856524737945498812416, coefficient := (-14020480856524737945498812416) }, { argument := 401771221210521025283883008, coefficient := (-401771221210521025283883008) }, { argument := 14020480856524737945498812416, coefficient := (-14020480856524737945498812416) }, { argument := 14020509983183218044970205184, coefficient := (-14020509983183218044970205184) }, { argument := 401778259736633955022012416, coefficient := (-401778259736633955022012416) }, { argument := 14025671430749741658423689216, coefficient := (-14025671430749741658423689216) }, { argument := 48976418723973041571674193920, coefficient := (-48976418723973041571674193920) }, { argument := 14020509983183218044970205184, coefficient := (-14020509983183218044970205184) }, { argument := 401903505619142064237182976, coefficient := (-401903505619142064237182976) }, { argument := 1401979780698700561766154240, coefficient := (-1401979780698700561766154240) }, { argument := 401778259736633955022012416, coefficient := (-401778259736633955022012416) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 57710227398420512212816756736, coefficient := 57710227398420512212816756736 }, { argument := 201513342017326616219809218560, coefficient := 201513342017326616219809218560 }, { argument := 57689080641310221941549826048, coefficient := 57689080641310221941549826048 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 4411247534245227247727280128, coefficient := 4411247534245227247727280128 }, { argument := 154044879154891167414261645312, coefficient := 154044879154891167414261645312 }, { argument := 154045200275812002550136176640, coefficient := 154045200275812002550136176640 }, { argument := 4411323092108953162050699264, coefficient := 4411323092108953162050699264 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8
