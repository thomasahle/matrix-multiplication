import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 20, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3288655729463252782915082222829568)
def positiveArguments : Array ℕ := #[
    203, 3647, 1365, 49, 5467, 5467,
    3913, 203, 1, 1, 2318825, 271025625,
    74202375, 231704135, 4518854405, 9037705495, 28963155, 407859,
    192825261, 7319493159, 771301573, 407859, 332899, 58387357,
    14596841, 83223
  ]
def positiveCoefficients : Array ℕ := #[
    7853182124216631118891319296, 141086478852305683204909563904, 211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144, 211494318586661686339797254144,
    151376855428865406740008534016, 7853182124216631118891319296, 39614081257132168796771975168, 39614081257132168796771975168, 1401643706833946248019024281600, 5119529309995189550280867840000,
    1401643234597297961054502912000, 1094191841066303461996321832960, 42679373166279706629394671861760, 42679357511634815916520788459520, 1094197059281267032954282967040, 30816954741387690035405389824,
    3642366198387965469233327898624, 34565329165655258830404965105664, 3642368696519834907275645943808, 30816954741387690035405389824, 3144142159561644043988369408, 551452995440288719110819282944,
    551453061553419479285852274688, 3144076046430883868955377664
  ]
def positiveScales : Array ℕ := #[
    7, 11, 10, 5, 12, 12,
    11, 7, 0, 0, 21, 28,
    26, 27, 32, 33, 24, 18,
    27, 32, 29, 18, 18, 25,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    7, 1, 25, 1105, 529, 7
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 79228162514264337593543950336, 7922816251426433759354395033600, 87547119578262093040866065121280, 41911697970045834586984749727744, 1109194275199700726309615304704
  ]
def negativeScales : Array ℕ := #[
    2, 0, 4, 10, 9, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7665335917183229, 11832494484259625, 10414685235807213, 5614709844114682, 12416533660199582, 12416533660199582,
    11934059394410200, 7665335917183229, 0, 0, 21144962514293498, 28013854021425970,
    26144962028225903, 27787708549885827, 32073309928904388, 33073309399728793, 24787715430100623, 18637710962028093,
    27522718822763017, 32769096605983640, 29522719812241017, 18637710962028093, 18344725011189521, 25799152670810491,
    23799152843773700, 16344694674746743
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 0, 4643856189792934, 10109830654278794, 9047123912114026, 2807354922807594
  ]

abbrev PositiveTerm := Fin 26
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 13324426611 / 250000000000
noncomputable def negativeCeiling : ℝ := 15735896091 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1401643706833946248019024281600, coefficient := 1401643706833946248019024281600 }, { argument := 5119529309995189550280867840000, coefficient := 5119529309995189550280867840000 }, { argument := 1401643234597297961054502912000, coefficient := 1401643234597297961054502912000 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 1094191841066303461996321832960, coefficient := 1094191841066303461996321832960 }, { argument := 42679373166279706629394671861760, coefficient := 42679373166279706629394671861760 }, { argument := 42679357511634815916520788459520, coefficient := 42679357511634815916520788459520 }, { argument := 1094197059281267032954282967040, coefficient := 1094197059281267032954282967040 }, { argument := 87547119578262093040866065121280, coefficient := (-87547119578262093040866065121280) }, { argument := 30816954741387690035405389824, coefficient := 30816954741387690035405389824 }, { argument := 3642366198387965469233327898624, coefficient := 3642366198387965469233327898624 }, { argument := 34565329165655258830404965105664, coefficient := 34565329165655258830404965105664 }, { argument := 3642368696519834907275645943808, coefficient := 3642368696519834907275645943808 }, { argument := 30816954741387690035405389824, coefficient := 30816954741387690035405389824 }, { argument := 41911697970045834586984749727744, coefficient := (-41911697970045834586984749727744) }, { argument := 3144142159561644043988369408, coefficient := 3144142159561644043988369408 }, { argument := 551452995440288719110819282944, coefficient := 551452995440288719110819282944 }, { argument := 551453061553419479285852274688, coefficient := 551453061553419479285852274688 }, { argument := 3144076046430883868955377664, coefficient := 3144076046430883868955377664 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }] }

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

end TermShard8


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
