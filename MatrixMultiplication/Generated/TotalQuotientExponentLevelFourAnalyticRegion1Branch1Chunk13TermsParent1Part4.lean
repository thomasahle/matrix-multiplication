import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

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
def constantNumerator : ℤ := (-273658212686275382538394998407168)
def positiveArguments : Array ℕ := #[
    1881, 93, 939, 1911, 93, 285,
    93, 93, 2253, 1707, 951, 93,
    951, 1899, 93, 2253, 93, 285,
    855, 1805, 4655, 3895, 108965, 3325,
    3895, 3515, 1805, 1805, 3515, 108965,
    3515, 285, 4655, 375, 5625, 9875,
    375, 3125, 375, 9875, 19625, 3125,
    302875, 19375, 5625, 9875, 375, 19375,
    375, 9875, 9875, 375, 243, 1107,
    27, 11583, 513, 27, 513, 999
  ]
def positiveCoefficients : Array ℕ := #[
    72767662934243759283914145792, 3597763239173136423925579776, 72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960,
    3597763239173136423925579776, 3597763239173136423925579776, 87158715890936304979616464896, 66036363970629504039150157824, 73580061085024790089316696064, 3597763239173136423925579776,
    73580061085024790089316696064, 73464004206341785688544903168, 3597763239173136423925579776, 87158715890936304979616464896, 3597763239173136423925579776, 88203227799083344586562600960,
    66152420849312508439921950720, 69827555340940981131028725760, 90040795044897580932115988480, 1205444113254139042683022213120, 2107689630948929088349735485440, 64314853603498272094368563200,
    1205444113254139042683022213120, 67989988095126744785475338240, 69827555340940981131028725760, 69827555340940981131028725760, 67989988095126744785475338240, 2107689630948929088349735485440,
    67989988095126744785475338240, 88203227799083344586562600960, 90040795044897580932115988480, 29014219670751100192948224000, 435213295061266502894223360000, 764041117996445638414303232000,
    29014219670751100192948224000, 483570327845851669882470400000, 29014219670751100192948224000, 764041117996445638414303232000, 759205414717987121715478528000, 483570327845851669882470400000,
    11716909043704985961252257792000, 749534008161070088317829120000, 435213295061266502894223360000, 764041117996445638414303232000, 29014219670751100192948224000, 749534008161070088317829120000,
    29014219670751100192948224000, 764041117996445638414303232000, 764041117996445638414303232000, 29014219670751100192948224000, 37602428693293425850060898304, 42824988234028623884791578624,
    33424381060705267422276354048, 448095608595079991379892371456, 39691452509587505063953170432, 33424381060705267422276354048, 39691452509587505063953170432, 38646940601440465457007034368
  ]
def positiveScales : Array ℕ := #[
    10, 6, 9, 10, 6, 8,
    6, 6, 11, 10, 9, 6,
    9, 10, 6, 11, 6, 8,
    9, 10, 12, 11, 16, 11,
    11, 11, 10, 10, 11, 16,
    11, 8, 12, 8, 12, 13,
    8, 11, 8, 13, 14, 11,
    18, 14, 12, 13, 8, 14,
    8, 13, 13, 8, 7, 10,
    4, 13, 9, 4, 9, 9
  ]
def negativeArguments : Array ℕ := #[
    3, 3, 95, 125
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 475368975085586025561263702016, 7526675438855112071386675281920, 19807040628566084398385987584000
  ]
def negativeScales : Array ℕ := #[
    1, 1, 6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10877284133344468, 6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103,
    6539158811107971, 6539158811107971, 11137631598235427, 10737247343017206, 9893301530621223, 6539158811107971,
    9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971, 8154818109052103,
    9739780609762119, 10817783121717284, 12184565452446155, 11927407612511617, 16733505284337084, 11699138625271509,
    11927407612511617, 11779308973933791, 10817783121717284, 10817783121717284, 11779308973933791, 16733505284337084,
    11779308973933791, 8154818109052103, 12184565452446155, 8550746785383158, 12457637380991757, 13269565032839189,
    8550746785383158, 11609640474436353, 8550746785383158, 13269565032839189, 14260405033553713, 11609640474436353,
    18208362974113433, 14241908689936324, 12457637380991757, 13269565032839189, 8550746785383158, 14241908689936324,
    8550746785383158, 13269565032839189, 13269565032839189, 8550746785383158, 7924812503187618, 10112439506781552,
    4754887502147955, 13499721339662996, 9002815015607054, 4754887502147955, 9002815015607054, 9964340866974576
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 1584962500724866, 6569855608333349, 6965784298236803
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 1339332757 / 250000000000
noncomputable def negativeCeiling : ℝ := 1137066797 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 66036363970629504039150157824, coefficient := 66036363970629504039150157824 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 73464004206341785688544903168, coefficient := 73464004206341785688544903168 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 66152420849312508439921950720, coefficient := 66152420849312508439921950720 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 90040795044897580932115988480, coefficient := 90040795044897580932115988480 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 2107689630948929088349735485440, coefficient := 2107689630948929088349735485440 }, { argument := 64314853603498272094368563200, coefficient := 64314853603498272094368563200 }, { argument := 1205444113254139042683022213120, coefficient := 1205444113254139042683022213120 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 69827555340940981131028725760, coefficient := 69827555340940981131028725760 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 2107689630948929088349735485440, coefficient := 2107689630948929088349735485440 }, { argument := 67989988095126744785475338240, coefficient := 67989988095126744785475338240 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 90040795044897580932115988480, coefficient := 90040795044897580932115988480 }, { argument := 7526675438855112071386675281920, coefficient := (-7526675438855112071386675281920) }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 435213295061266502894223360000, coefficient := 435213295061266502894223360000 }, { argument := 764041117996445638414303232000, coefficient := 764041117996445638414303232000 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 483570327845851669882470400000, coefficient := 483570327845851669882470400000 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 764041117996445638414303232000, coefficient := 764041117996445638414303232000 }, { argument := 759205414717987121715478528000, coefficient := 759205414717987121715478528000 }, { argument := 483570327845851669882470400000, coefficient := 483570327845851669882470400000 }, { argument := 11716909043704985961252257792000, coefficient := 11716909043704985961252257792000 }, { argument := 749534008161070088317829120000, coefficient := 749534008161070088317829120000 }, { argument := 435213295061266502894223360000, coefficient := 435213295061266502894223360000 }, { argument := 764041117996445638414303232000, coefficient := 764041117996445638414303232000 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 749534008161070088317829120000, coefficient := 749534008161070088317829120000 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 764041117996445638414303232000, coefficient := 764041117996445638414303232000 }, { argument := 764041117996445638414303232000, coefficient := 764041117996445638414303232000 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 19807040628566084398385987584000, coefficient := (-19807040628566084398385987584000) }, { argument := 37602428693293425850060898304, coefficient := 37602428693293425850060898304 }, { argument := 42824988234028623884791578624, coefficient := 42824988234028623884791578624 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 448095608595079991379892371456, coefficient := 448095608595079991379892371456 }, { argument := 39691452509587505063953170432, coefficient := 39691452509587505063953170432 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 39691452509587505063953170432, coefficient := 39691452509587505063953170432 }, { argument := 38646940601440465457007034368, coefficient := 38646940601440465457007034368 }] }

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

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-280671977020767553539617378961195008)
def positiveArguments : Array ℕ := #[
    18873, 999, 11583, 18873, 243, 999,
    999, 1107, 15, 7172259721, 7172259959, 41416888637,
    75727047619, 41414448957, 8573762323, 671993308007, 671993380891, 2143454411,
    46361485, 9310788139, 192226291121, 18621607877, 46361485, 2101943,
    393735497, 12599536583, 67261497, 3198807, 144580257, 401985
  ]
def positiveCoefficients : Array ℕ := #[
    1460227647589561370510698217472, 38646940601440465457007034368, 448095608595079991379892371456, 1460227647589561370510698217472, 37602428693293425850060898304, 38646940601440465457007034368,
    38646940601440465457007034368, 42824988234028623884791578624, 2376844875427930127806318510080, 67740077825772785719504516677632, 67740080073619231565455638396928, 391171453448226928006694598344704,
    1430443486090556683468769691959296, 391148411322105073174624698630144, 80976895652451578107128096751616, 3173398674444954785318029462863872, 3173399018629913522789251217883136, 80977418144523975770413830504448,
    875743691440255254120355594240, 175875815346855357355275348606976, 1815525988632306560683823104786432, 175876113790972341751113563766784, 875743691440255254120355594240, 317636645507279061421177962496,
    59499626052762295821704504541184, 59499629259249137690193604640768, 317633439020437192932077862912, 30211877923937602394174521344, 1365521919482958804989975199744, 30373127849861669299641384960
  ]
def positiveScales : Array ℕ := #[
    14, 9, 13, 14, 7, 9,
    9, 10, 3, 32, 32, 35,
    36, 35, 32, 39, 39, 30,
    25, 33, 37, 34, 25, 21,
    28, 33, 26, 21, 27, 18
  ]
def negativeArguments : Array ℕ := #[
    27, 15, 855, 27929, 10269, 27377,
    755, 9
  ]
def negativeCoefficients : Array ℕ := #[
    4278320775770274230051373318144, 2376844875427930127806318510080, 135480157899392017284960155074560, 2212763350860888684650088988934144, 6508752006871843861984822608003072, 2169029405153014770298452728348672,
    119634525396539149766251365007360, 1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    4, 3, 9, 14, 13, 14,
    9, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14204036147538904, 9964340866974576, 13499721339662996, 14204036147538904, 7924812503187618, 9964340866974576,
    9964340866974576, 10112439506781552, 3906890595303263, 32739780585825352, 32739780633698885, 35269500126850915,
    36140089632126533, 35269415141763372, 32997281276720146, 39289655909870398, 39289656066344247, 30997290585477502,
    25466423442113806, 33116256148096994, 37484014713253946, 34116258596207790, 25466423442113806, 21003292116487102,
    28552651542810728, 33552651620558823, 26003277552657392, 21609102519407016, 27107295319182915, 18616782142931597
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4754887502413606, 3906890600547867, 9739780609952834, 14769476298627000, 13326008077730995, 14740676742973726,
    9560332834214255, 3169925001442313
  ]

abbrev PositiveTerm := Fin 30
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 5079628688673 / 1000000000000
noncomputable def negativeCeiling : ℝ := 926176349189 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1460227647589561370510698217472, coefficient := 1460227647589561370510698217472 }, { argument := 38646940601440465457007034368, coefficient := 38646940601440465457007034368 }, { argument := 448095608595079991379892371456, coefficient := 448095608595079991379892371456 }, { argument := 1460227647589561370510698217472, coefficient := 1460227647589561370510698217472 }, { argument := 37602428693293425850060898304, coefficient := 37602428693293425850060898304 }, { argument := 38646940601440465457007034368, coefficient := 38646940601440465457007034368 }, { argument := 38646940601440465457007034368, coefficient := 38646940601440465457007034368 }, { argument := 42824988234028623884791578624, coefficient := 42824988234028623884791578624 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 2376844875427930127806318510080, coefficient := 2376844875427930127806318510080 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 67740077825772785719504516677632, coefficient := 67740077825772785719504516677632 }, { argument := 67740080073619231565455638396928, coefficient := 67740080073619231565455638396928 }, { argument := 135480157899392017284960155074560, coefficient := (-135480157899392017284960155074560) }, { argument := 391171453448226928006694598344704, coefficient := 391171453448226928006694598344704 }, { argument := 1430443486090556683468769691959296, coefficient := 1430443486090556683468769691959296 }, { argument := 391148411322105073174624698630144, coefficient := 391148411322105073174624698630144 }, { argument := 2212763350860888684650088988934144, coefficient := (-2212763350860888684650088988934144) }, { argument := 80976895652451578107128096751616, coefficient := 80976895652451578107128096751616 }, { argument := 3173398674444954785318029462863872, coefficient := 3173398674444954785318029462863872 }, { argument := 3173399018629913522789251217883136, coefficient := 3173399018629913522789251217883136 }, { argument := 80977418144523975770413830504448, coefficient := 80977418144523975770413830504448 }, { argument := 6508752006871843861984822608003072, coefficient := (-6508752006871843861984822608003072) }, { argument := 875743691440255254120355594240, coefficient := 875743691440255254120355594240 }, { argument := 175875815346855357355275348606976, coefficient := 175875815346855357355275348606976 }, { argument := 1815525988632306560683823104786432, coefficient := 1815525988632306560683823104786432 }, { argument := 175876113790972341751113563766784, coefficient := 175876113790972341751113563766784 }, { argument := 875743691440255254120355594240, coefficient := 875743691440255254120355594240 }, { argument := 2169029405153014770298452728348672, coefficient := (-2169029405153014770298452728348672) }, { argument := 317636645507279061421177962496, coefficient := 317636645507279061421177962496 }, { argument := 59499626052762295821704504541184, coefficient := 59499626052762295821704504541184 }, { argument := 59499629259249137690193604640768, coefficient := 59499629259249137690193604640768 }, { argument := 317633439020437192932077862912, coefficient := 317633439020437192932077862912 }, { argument := 119634525396539149766251365007360, coefficient := (-119634525396539149766251365007360) }, { argument := 30211877923937602394174521344, coefficient := 30211877923937602394174521344 }, { argument := 1365521919482958804989975199744, coefficient := 1365521919482958804989975199744 }, { argument := 30373127849861669299641384960, coefficient := 30373127849861669299641384960 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }] }

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

end TermShard9


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
