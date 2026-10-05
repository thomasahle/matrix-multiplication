import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 8, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8

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
def constantNumerator : ℤ := (-7253971694864087191645035954176)
def positiveArguments : Array ℕ := #[
    9, 16777211, 16777221, 61850589, 211843081, 30925325,
    115869, 65254951, 32629071, 1850731
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 633825111219455385962543054848, 633825489008774015534160150528, 584162296878691933376256933888, 2000801330684478726892528074752, 584162873007402843472973004800,
    17509628224115933480503738368, 616315586887402075614234017792, 616345725030295749689987825664, 17479660086415642711977623552
  ]
def positiveScales : Array ℕ := #[
    3, 23, 24, 25, 27, 24,
    16, 25, 24, 20
  ]
def negativeArguments : Array ℕ := #[
    3887916582097, 547398043822819, 273712405978525, 15525049190047, 95636349749195, 327567547255847,
    47818224342535, 3887916582097, 3887920380719, 3887920380719, 547398364173597, 273712566067811,
    15525064554849, 327567547255847, 1121933155752627, 163783930506387, 547398043822819, 547398364173597,
    47818224342535, 163783930506387, 23909136924339, 273712405978525, 273712566067811, 15525049190047,
    15525064554849, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4377404917594905404954902528, 154078851636486630508293259264, 154086386196445888946949324800, 4369912859200268121074040832, 53838478636693628823367843840, 184404135470012486094646411264,
    53838534332639851770114211840, 4377404917594905404954902528, 4377409194463061335296966656, 4377409194463061335296966656, 154078941807214407298823749632, 154086476318701985898044588032,
    4369917184007553234914770944, 184404135470012486094646411264, 631592217772766950992981786624, 184404312099459926358635839488, 154078851636486630508293259264, 154078941807214407298823749632,
    53838534332639851770114211840, 184404312099459926358635839488, 53838590071601643607736451072, 154086386196445888946949324800, 154086476318701985898044588032, 4369912859200268121074040832,
    4369917184007553234914770944, 1267650600228229401496703205376, 3169126500570573503741758013440, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    41, 48, 47, 43, 46, 48,
    45, 41, 41, 41, 48, 47,
    43, 48, 49, 47, 48, 48,
    45, 47, 44, 47, 47, 43,
    43, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 23999999568583737, 24000000429956563, 25882283997993879, 27658420768752581, 24882285420847811,
    16822135108635254, 25959584028926499, 24959654575715523, 20819663786910664
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41822134404925410, 48959583619775994, 47959654166827899, 43819663074027960, 46442624299812459, 48218785761921468,
    45442625792280781, 41822134404925410, 41822135814485116, 41822135814485116, 48959584464076487, 47959655010633271,
    43819664501831043, 48218785761921468, 49994908168553773, 47218787143790184, 48959583619775994, 48959584464076487,
    45442625792280781, 47218787143790184, 44442627285900232, 47959654166827899, 47959655010633271, 43819663074027960,
    43819664501831043, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 188380297 / 100000000000
noncomputable def negativeCeiling : ℝ := 873600889 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4377404917594905404954902528, coefficient := (-4377404917594905404954902528) }, { argument := 154078851636486630508293259264, coefficient := (-154078851636486630508293259264) }, { argument := 154086386196445888946949324800, coefficient := (-154086386196445888946949324800) }, { argument := 4369912859200268121074040832, coefficient := (-4369912859200268121074040832) }, { argument := 53838478636693628823367843840, coefficient := (-53838478636693628823367843840) }, { argument := 184404135470012486094646411264, coefficient := (-184404135470012486094646411264) }, { argument := 53838534332639851770114211840, coefficient := (-53838534332639851770114211840) }, { argument := 4377404917594905404954902528, coefficient := (-4377404917594905404954902528) }, { argument := 4377409194463061335296966656, coefficient := (-4377409194463061335296966656) }, { argument := 4377409194463061335296966656, coefficient := (-4377409194463061335296966656) }, { argument := 154078941807214407298823749632, coefficient := (-154078941807214407298823749632) }, { argument := 154086476318701985898044588032, coefficient := (-154086476318701985898044588032) }, { argument := 4369917184007553234914770944, coefficient := (-4369917184007553234914770944) }, { argument := 184404135470012486094646411264, coefficient := (-184404135470012486094646411264) }, { argument := 631592217772766950992981786624, coefficient := (-631592217772766950992981786624) }, { argument := 184404312099459926358635839488, coefficient := (-184404312099459926358635839488) }, { argument := 154078851636486630508293259264, coefficient := (-154078851636486630508293259264) }, { argument := 154078941807214407298823749632, coefficient := (-154078941807214407298823749632) }, { argument := 53838534332639851770114211840, coefficient := (-53838534332639851770114211840) }, { argument := 184404312099459926358635839488, coefficient := (-184404312099459926358635839488) }, { argument := 53838590071601643607736451072, coefficient := (-53838590071601643607736451072) }, { argument := 154086386196445888946949324800, coefficient := (-154086386196445888946949324800) }, { argument := 154086476318701985898044588032, coefficient := (-154086476318701985898044588032) }, { argument := 4369912859200268121074040832, coefficient := (-4369912859200268121074040832) }, { argument := 4369917184007553234914770944, coefficient := (-4369917184007553234914770944) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 633825111219455385962543054848, coefficient := 633825111219455385962543054848 }, { argument := 633825489008774015534160150528, coefficient := 633825489008774015534160150528 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 584162296878691933376256933888, coefficient := 584162296878691933376256933888 }, { argument := 2000801330684478726892528074752, coefficient := 2000801330684478726892528074752 }, { argument := 584162873007402843472973004800, coefficient := 584162873007402843472973004800 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 17509628224115933480503738368, coefficient := 17509628224115933480503738368 }, { argument := 616315586887402075614234017792, coefficient := 616315586887402075614234017792 }, { argument := 616345725030295749689987825664, coefficient := 616345725030295749689987825664 }, { argument := 17479660086415642711977623552, coefficient := 17479660086415642711977623552 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8
