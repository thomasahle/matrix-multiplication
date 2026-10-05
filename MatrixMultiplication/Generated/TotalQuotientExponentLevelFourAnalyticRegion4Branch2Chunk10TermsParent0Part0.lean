import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10

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
def constantNumerator : ℤ := (-998576568555641012407660183552)
def positiveArguments : Array ℕ := #[
    5, 1048581, 1048571, 1497863, 43145101, 11980859,
    763291, 8197797, 32791149, 190809, 33993, 1187969,
    14333263, 1187997, 16997
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 79228540303582967165161046016, 79227784724945708021926854656, 113175328434089206219557306368, 407493957724851225158161006592, 113156013955174269370633289728,
    7209079670152108729614467072, 309704014289354631391211421696, 309703645944768967558884753408, 7208560209838993068640960512, 321054807704375699498336256, 11220049976576339109738446848,
    135373841562711239129191940096, 11220314429099379809870413824, 321064252437341438788763648
  ]
def positiveScales : Array ℕ := #[
    2, 20, 19, 20, 25, 23,
    19, 22, 24, 17, 15, 20,
    23, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    35644413933, 1245681721989, 15029587249803, 1245711082257, 17822731257, 2280452575933,
    12279946770513, 98239455747507, 285035778465, 2280452575933, 8245353820459, 285011447683,
    35644413933, 35644074003, 35644074003, 1245669842299, 15029443917173, 1245699202287,
    17822561287, 8245353820459, 353682489384837, 353682071879151, 8244763734369, 12279946770513,
    353682489384837, 98222780423667, 1245681721989, 1245669842299, 285011447683, 98222780423667,
    49111331017263, 2279925268887, 98239455747507, 353682071879151, 49111331017263, 15029587249803,
    15029443917173, 285035778465, 8244763734369, 2279925268887, 1245711082257, 1245699202287,
    17822731257, 17822561287, 1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    80264084653249257887760384, 2805025869485949096686518272, 33843621768872574290592006144, 2805091982931961245635444736, 80266445847749691778793472, 641890335700496658410242048,
    27651981849905936278669492224, 27651948518597053548532334592, 641843512841116624166584320, 641890335700496658410242048, 2320860774584815498616111104, 641788724790742207780880384,
    80264084653249257887760384, 80263319198938591861407744, 80263319198938591861407744, 2804999118802220458182705152, 33843299012483045274003963904, 2805065231617728659299762176,
    80265680370921027615588352, 2320860774584815498616111104, 99552770462563832515182723072, 99552652945160589098725933056, 2320694680116375466555736064, 27651981849905936278669492224,
    99552770462563832515182723072, 27647254832207546901753495552, 2805025869485949096686518272, 2804999118802220458182705152, 641788724790742207780880384, 27647254832207546901753495552,
    27647221508626841132184109056, 641741911962004443598159872, 27651948518597053548532334592, 99552652945160589098725933056, 27647221508626841132184109056, 33843621768872574290592006144,
    33843299012483045274003963904, 641843512841116624166584320, 2320694680116375466555736064, 641741911962004443598159872, 2805091982931961245635444736, 2805065231617728659299762176,
    80266445847749691778793472, 80265680370921027615588352, 158456325028528675187087900672, 633825300114114700748351602688, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 40, 43, 40, 34, 41,
    43, 46, 38, 41, 42, 38,
    35, 35, 35, 40, 43, 40,
    34, 42, 48, 48, 42, 43,
    48, 46, 40, 40, 38, 46,
    45, 41, 46, 48, 45, 43,
    43, 38, 42, 41, 40, 40,
    34, 34, 0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 20000006879289633, 19999993119218142, 20514474245017215, 25362693419113981, 23514228013958614,
    19541873654981504, 22966804833790256, 24966803117928688, 17541769695828102, 15052950069882485, 20180065758888953,
    23772863743993937, 20180099762288957, 14052992510203163
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35052956949172119, 40180072638178587, 43772870623674108, 40180106641578591, 34052999389492797, 41052457307012099,
    43481369540654097, 46481367801648796, 38052352065404371, 41052457307012099, 42906718546764668, 38052228911051737,
    35052956949172119, 35052943190560049, 35052943190560049, 40180058879566518, 43772856865061931, 40180092882966522,
    34052985630880728, 42906718546764668, 48329448122234273, 48329446419199047, 42906615295305393, 43481369540654097,
    48329448122234273, 46481122895477148, 40180072638178587, 40180058879566518, 38052228911051737, 46481122895477148,
    45481121156577792, 41052123675330880, 46481367801648796, 48329446419199047, 45481121156577792, 43772870623674108,
    43772856865061931, 38052352065404371, 42906615295305393, 41052123675330880, 40180106641578591, 40180092882966522,
    34052999389492797, 34052985630880728, 0, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 18835291 / 40000000000
noncomputable def negativeCeiling : ℝ := 221220381 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 80264084653249257887760384, coefficient := (-80264084653249257887760384) }, { argument := 2805025869485949096686518272, coefficient := (-2805025869485949096686518272) }, { argument := 33843621768872574290592006144, coefficient := (-33843621768872574290592006144) }, { argument := 2805091982931961245635444736, coefficient := (-2805091982931961245635444736) }, { argument := 80266445847749691778793472, coefficient := (-80266445847749691778793472) }, { argument := 641890335700496658410242048, coefficient := (-641890335700496658410242048) }, { argument := 27651981849905936278669492224, coefficient := (-27651981849905936278669492224) }, { argument := 27651948518597053548532334592, coefficient := (-27651948518597053548532334592) }, { argument := 641843512841116624166584320, coefficient := (-641843512841116624166584320) }, { argument := 641890335700496658410242048, coefficient := (-641890335700496658410242048) }, { argument := 2320860774584815498616111104, coefficient := (-2320860774584815498616111104) }, { argument := 641788724790742207780880384, coefficient := (-641788724790742207780880384) }, { argument := 80264084653249257887760384, coefficient := (-80264084653249257887760384) }, { argument := 80263319198938591861407744, coefficient := (-80263319198938591861407744) }, { argument := 80263319198938591861407744, coefficient := (-80263319198938591861407744) }, { argument := 2804999118802220458182705152, coefficient := (-2804999118802220458182705152) }, { argument := 33843299012483045274003963904, coefficient := (-33843299012483045274003963904) }, { argument := 2805065231617728659299762176, coefficient := (-2805065231617728659299762176) }, { argument := 80265680370921027615588352, coefficient := (-80265680370921027615588352) }, { argument := 2320860774584815498616111104, coefficient := (-2320860774584815498616111104) }, { argument := 99552770462563832515182723072, coefficient := (-99552770462563832515182723072) }, { argument := 99552652945160589098725933056, coefficient := (-99552652945160589098725933056) }, { argument := 2320694680116375466555736064, coefficient := (-2320694680116375466555736064) }, { argument := 27651981849905936278669492224, coefficient := (-27651981849905936278669492224) }, { argument := 99552770462563832515182723072, coefficient := (-99552770462563832515182723072) }, { argument := 27647254832207546901753495552, coefficient := (-27647254832207546901753495552) }, { argument := 2805025869485949096686518272, coefficient := (-2805025869485949096686518272) }, { argument := 2804999118802220458182705152, coefficient := (-2804999118802220458182705152) }, { argument := 641788724790742207780880384, coefficient := (-641788724790742207780880384) }, { argument := 27647254832207546901753495552, coefficient := (-27647254832207546901753495552) }, { argument := 27647221508626841132184109056, coefficient := (-27647221508626841132184109056) }, { argument := 641741911962004443598159872, coefficient := (-641741911962004443598159872) }, { argument := 27651948518597053548532334592, coefficient := (-27651948518597053548532334592) }, { argument := 99552652945160589098725933056, coefficient := (-99552652945160589098725933056) }, { argument := 27647221508626841132184109056, coefficient := (-27647221508626841132184109056) }, { argument := 33843621768872574290592006144, coefficient := (-33843621768872574290592006144) }, { argument := 33843299012483045274003963904, coefficient := (-33843299012483045274003963904) }, { argument := 641843512841116624166584320, coefficient := (-641843512841116624166584320) }, { argument := 2320694680116375466555736064, coefficient := (-2320694680116375466555736064) }, { argument := 641741911962004443598159872, coefficient := (-641741911962004443598159872) }, { argument := 2805091982931961245635444736, coefficient := (-2805091982931961245635444736) }, { argument := 2805065231617728659299762176, coefficient := (-2805065231617728659299762176) }, { argument := 80266445847749691778793472, coefficient := (-80266445847749691778793472) }, { argument := 80265680370921027615588352, coefficient := (-80265680370921027615588352) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 79228540303582967165161046016, coefficient := 79228540303582967165161046016 }, { argument := 79227784724945708021926854656, coefficient := 79227784724945708021926854656 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 113175328434089206219557306368, coefficient := 113175328434089206219557306368 }, { argument := 407493957724851225158161006592, coefficient := 407493957724851225158161006592 }, { argument := 113156013955174269370633289728, coefficient := 113156013955174269370633289728 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 7209079670152108729614467072, coefficient := 7209079670152108729614467072 }, { argument := 309704014289354631391211421696, coefficient := 309704014289354631391211421696 }, { argument := 309703645944768967558884753408, coefficient := 309703645944768967558884753408 }, { argument := 7208560209838993068640960512, coefficient := 7208560209838993068640960512 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 321054807704375699498336256, coefficient := 321054807704375699498336256 }, { argument := 11220049976576339109738446848, coefficient := 11220049976576339109738446848 }, { argument := 135373841562711239129191940096, coefficient := 135373841562711239129191940096 }, { argument := 11220314429099379809870413824, coefficient := 11220314429099379809870413824 }, { argument := 321064252437341438788763648, coefficient := 321064252437341438788763648 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk10
