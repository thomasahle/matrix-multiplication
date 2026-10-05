import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5

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
def constantNumerator : ℤ := (-2085788649269932033014233038848)
def positiveArguments : Array ℕ := #[
    9, 8388589, 8388627, 1926895, 53056707, 15414213,
    476401, 16300815, 8150397, 238211
  ]
def positiveCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 316911932257351954188103319552, 316913367856762746560248283136, 291184139648291360449432125440, 1002212859312941141188084236288, 291166251324054250233362644992,
    8998960459222327397799952384, 307913689597835022976375848960, 307913292919050461926177898496, 8999357138006888447997902848
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 20, 25, 23,
    18, 23, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    1998166085323, 68370418708801, 34185165314297, 999127082753, 23761771590991, 163579568225901,
    47520357586677, 1998166085323, 1998175154485, 1998175154485, 68370728406719, 34185320163079,
    999131617535, 163579568225901, 17593568420729, 163570075898483, 68370418708801, 68370728406719,
    47520357586677, 163570075898483, 5939643435731, 34185165314297, 34185320163079, 999127082753,
    999131617535, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2249735009321256379117207552, 76978248055030242966790733824, 76978148885533386987752390656, 2249834178791090760391327744, 26753376420712476371933200384, 92087110313449296381043802112,
    26751583089983907471739060224, 2249735009321256379117207552, 2249745220289907319782768640, 2249745220289907319782768640, 76978596743887268521397190656, 76978497573991843975336558592,
    2249844390212353463607623680, 92087110313449296381043802112, 316937552734849800774757646336, 92081766608171473438240669696, 76978248055030242966790733824, 76978596743887268521397190656,
    26751583089983907471739060224, 92081766608171473438240669696, 26749775963871744206701592576, 76978148885533386987752390656, 76978497573991843975336558592, 2249834178791090760391327744,
    2249844390212353463607623680, 633825300114114700748351602688, 1584563250285286751870879006720, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    40, 45, 44, 39, 44, 47,
    45, 40, 40, 40, 45, 44,
    39, 47, 44, 47, 45, 45,
    45, 47, 42, 44, 44, 39,
    39, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 22999996730866427, 23000003267666665, 20877846527852203, 25661031800722547, 23877757896001039,
    18861816915828728, 23958440760875245, 22958438902280138, 17861880509163036
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40861813644122191, 45958437506139710, 44958435647543732, 39861877237458447, 44433707635762665, 47216985889294534,
    45433610925873585, 40861813644122191, 40861820192129376, 40861820192129376, 45958444041111072, 44958442182516044,
    39861883785467240, 47216985889294534, 44000113361073694, 47216902168991350, 45958437506139710, 45958444041111072,
    45433610925873585, 47216902168991350, 42433513465475293, 44958435647543732, 44958442182516044, 39861877237458447,
    39861883785467240, 0, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 54636953 / 62500000000
noncomputable def negativeCeiling : ℝ := 824442139 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2249735009321256379117207552, coefficient := (-2249735009321256379117207552) }, { argument := 76978248055030242966790733824, coefficient := (-76978248055030242966790733824) }, { argument := 76978148885533386987752390656, coefficient := (-76978148885533386987752390656) }, { argument := 2249834178791090760391327744, coefficient := (-2249834178791090760391327744) }, { argument := 26753376420712476371933200384, coefficient := (-26753376420712476371933200384) }, { argument := 92087110313449296381043802112, coefficient := (-92087110313449296381043802112) }, { argument := 26751583089983907471739060224, coefficient := (-26751583089983907471739060224) }, { argument := 2249735009321256379117207552, coefficient := (-2249735009321256379117207552) }, { argument := 2249745220289907319782768640, coefficient := (-2249745220289907319782768640) }, { argument := 2249745220289907319782768640, coefficient := (-2249745220289907319782768640) }, { argument := 76978596743887268521397190656, coefficient := (-76978596743887268521397190656) }, { argument := 76978497573991843975336558592, coefficient := (-76978497573991843975336558592) }, { argument := 2249844390212353463607623680, coefficient := (-2249844390212353463607623680) }, { argument := 92087110313449296381043802112, coefficient := (-92087110313449296381043802112) }, { argument := 316937552734849800774757646336, coefficient := (-316937552734849800774757646336) }, { argument := 92081766608171473438240669696, coefficient := (-92081766608171473438240669696) }, { argument := 76978248055030242966790733824, coefficient := (-76978248055030242966790733824) }, { argument := 76978596743887268521397190656, coefficient := (-76978596743887268521397190656) }, { argument := 26751583089983907471739060224, coefficient := (-26751583089983907471739060224) }, { argument := 92081766608171473438240669696, coefficient := (-92081766608171473438240669696) }, { argument := 26749775963871744206701592576, coefficient := (-26749775963871744206701592576) }, { argument := 76978148885533386987752390656, coefficient := (-76978148885533386987752390656) }, { argument := 76978497573991843975336558592, coefficient := (-76978497573991843975336558592) }, { argument := 2249834178791090760391327744, coefficient := (-2249834178791090760391327744) }, { argument := 2249844390212353463607623680, coefficient := (-2249844390212353463607623680) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 316911932257351954188103319552, coefficient := 316911932257351954188103319552 }, { argument := 316913367856762746560248283136, coefficient := 316913367856762746560248283136 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 291184139648291360449432125440, coefficient := 291184139648291360449432125440 }, { argument := 1002212859312941141188084236288, coefficient := 1002212859312941141188084236288 }, { argument := 291166251324054250233362644992, coefficient := 291166251324054250233362644992 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 8998960459222327397799952384, coefficient := 8998960459222327397799952384 }, { argument := 307913689597835022976375848960, coefficient := 307913689597835022976375848960 }, { argument := 307913292919050461926177898496, coefficient := 307913292919050461926177898496 }, { argument := 8999357138006888447997902848, coefficient := 8999357138006888447997902848 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5
