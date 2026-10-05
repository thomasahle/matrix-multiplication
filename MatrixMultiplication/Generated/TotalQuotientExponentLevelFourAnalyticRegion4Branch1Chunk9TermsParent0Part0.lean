import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 9, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9

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
def constantNumerator : ℤ := 5740678852885451480825197494272
def positiveArguments : Array ℕ := #[
    9, 25165807, 25165841, 46232995, 159185851, 23119697,
    3444739, 122384355, 122392319, 3436827, 101411, 1919099,
    21226201, 119945, 101397
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 237684326982332595212694585344, 237684648103253430348569116672, 436658291981359785633162199040, 1503467854618962790820549230592, 436718728827607551352607080448,
    32534639991667797567563890688, 1155887552159240157114044252160, 1155962770012579304823008002048, 32459913264442868301702365184, 957799814788587181532250112, 36250755179634613039835119616,
    400951600644216584418396995584, 36251151858419174090033070080, 957667588527066831466266624
  ]
def positiveScales : Array ℕ := #[
    3, 24, 24, 25, 27, 24,
    21, 26, 26, 21, 16, 20,
    24, 16, 16
  ]
def negativeArguments : Array ℕ := #[
    850696233919, 16098558178591, 178058159895349, 2012341792375, 850578793513, 10612951128215,
    377217439656235, 377242141874295, 10588410783175, 10612951128215, 36565661934895, 5307258601757,
    850696233919, 850698017857, 850698017857, 16098580269793, 178058399141067, 2012344553865,
    850580577239, 36565661934895, 1298781766909711, 1298865976182103, 36482001344107, 377217439656235,
    1298781766909711, 188634776144867, 16098558178591, 16098580269793, 5307258601757, 188634776144867,
    188647127273753, 5294988403175, 377242141874295, 1298865976182103, 188647127273753, 178058159895349,
    178058399141067, 10588410783175, 36482001344107, 5294988403175, 2012341792375, 2012344553865,
    850578793513, 850580577239, 3, 15, 15, 3
  ]
def negativeCoefficients : Array ℕ := #[
    239449702630193293755940864, 9062682576788084799561531392, 100237832819371243930426277888, 9062781746282126028832768000, 239416646094649553770774528, 2987280171645647444812759040,
    106177270042092031671701340160, 106184223098345171717738987520, 2980372678597041982328012800, 2987280171645647444812759040, 10292318841534290735524741120, 2987720982653960603444445184,
    239449702630193293755940864, 239450204764100297010184192, 239450204764100297010184192, 9062695013029221720356028416, 100237967502737048278772219904, 9062794182927461016183767040,
    239417148168883861962358784, 10292318841534290735524741120, 365574567593135553236923580416, 365598270396120912724196589568, 10268770478690638713629704192, 106177270042092031671701340160,
    365574567593135553236923580416, 106191938444392493648397205504, 9062682576788084799561531392, 9062695013029221720356028416, 2987720982653960603444445184, 106191938444392493648397205504,
    106198891511823567969568423936, 2980813474933753454893465600, 106184223098345171717738987520, 365598270396120912724196589568, 106198891511823567969568423936, 100237832819371243930426277888,
    100237967502737048278772219904, 2980372678597041982328012800, 10268770478690638713629704192, 2980813474933753454893465600, 9062781746282126028832768000, 9062794182927461016183767040,
    239416646094649553770774528, 239417148168883861962358784, 475368975085586025561263702016, 2376844875427930127806318510080, 2376844875427930127806318510080, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 43, 47, 40, 39, 43,
    48, 48, 43, 43, 45, 42,
    39, 39, 39, 43, 47, 40,
    39, 45, 50, 50, 45, 48,
    50, 47, 43, 43, 42, 47,
    47, 42, 48, 50, 47, 47,
    47, 43, 45, 42, 40, 40,
    39, 39, 1, 3, 3, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 24584961526152240, 24584963475288950, 25462419488426964, 27246136868854312, 24462619154633952,
    21715963246682576, 26866843901896134, 26866937780312654, 21712645801731377, 16629854623668130, 20871997706503085,
    24339342849449208, 16872013493301998, 16629655442860626
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39629853110992873, 43871996719418936, 47339341880219562, 40872012506197324, 39629653930156230, 43270891113731518,
    48422389705188884, 48422484177492979, 43267551304708852, 43270891113731518, 45055554712382162, 42271103985943721,
    39629853110992873, 39629856136368683, 39629856136368683, 43871998699151960, 47339343818678206, 40872014485973028,
    39629656955590178, 45055554712382162, 50206080459756668, 50206173996919312, 45052250109146362, 48422389705188884,
    50206080459756668, 47422588999911891, 43871996719418936, 43871998699151960, 42271103985943721, 47422588999911891,
    47422683459318707, 42267764663149202, 48422484177492979, 50206173996919312, 47422683459318707, 47339341880219562,
    47339343818678206, 43267551304708852, 45052250109146362, 42267764663149202, 40872012506197324, 40872014485973028,
    39629653930156230, 39629656955590178, 1584962500724866, 3906890600547867, 3906890600547867, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 1903975951 / 1000000000000
noncomputable def negativeCeiling : ℝ := 479106959 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 239449702630193293755940864, coefficient := (-239449702630193293755940864) }, { argument := 9062682576788084799561531392, coefficient := (-9062682576788084799561531392) }, { argument := 100237832819371243930426277888, coefficient := (-100237832819371243930426277888) }, { argument := 9062781746282126028832768000, coefficient := (-9062781746282126028832768000) }, { argument := 239416646094649553770774528, coefficient := (-239416646094649553770774528) }, { argument := 2987280171645647444812759040, coefficient := (-2987280171645647444812759040) }, { argument := 106177270042092031671701340160, coefficient := (-106177270042092031671701340160) }, { argument := 106184223098345171717738987520, coefficient := (-106184223098345171717738987520) }, { argument := 2980372678597041982328012800, coefficient := (-2980372678597041982328012800) }, { argument := 2987280171645647444812759040, coefficient := (-2987280171645647444812759040) }, { argument := 10292318841534290735524741120, coefficient := (-10292318841534290735524741120) }, { argument := 2987720982653960603444445184, coefficient := (-2987720982653960603444445184) }, { argument := 239449702630193293755940864, coefficient := (-239449702630193293755940864) }, { argument := 239450204764100297010184192, coefficient := (-239450204764100297010184192) }, { argument := 239450204764100297010184192, coefficient := (-239450204764100297010184192) }, { argument := 9062695013029221720356028416, coefficient := (-9062695013029221720356028416) }, { argument := 100237967502737048278772219904, coefficient := (-100237967502737048278772219904) }, { argument := 9062794182927461016183767040, coefficient := (-9062794182927461016183767040) }, { argument := 239417148168883861962358784, coefficient := (-239417148168883861962358784) }, { argument := 10292318841534290735524741120, coefficient := (-10292318841534290735524741120) }, { argument := 365574567593135553236923580416, coefficient := (-365574567593135553236923580416) }, { argument := 365598270396120912724196589568, coefficient := (-365598270396120912724196589568) }, { argument := 10268770478690638713629704192, coefficient := (-10268770478690638713629704192) }, { argument := 106177270042092031671701340160, coefficient := (-106177270042092031671701340160) }, { argument := 365574567593135553236923580416, coefficient := (-365574567593135553236923580416) }, { argument := 106191938444392493648397205504, coefficient := (-106191938444392493648397205504) }, { argument := 9062682576788084799561531392, coefficient := (-9062682576788084799561531392) }, { argument := 9062695013029221720356028416, coefficient := (-9062695013029221720356028416) }, { argument := 2987720982653960603444445184, coefficient := (-2987720982653960603444445184) }, { argument := 106191938444392493648397205504, coefficient := (-106191938444392493648397205504) }, { argument := 106198891511823567969568423936, coefficient := (-106198891511823567969568423936) }, { argument := 2980813474933753454893465600, coefficient := (-2980813474933753454893465600) }, { argument := 106184223098345171717738987520, coefficient := (-106184223098345171717738987520) }, { argument := 365598270396120912724196589568, coefficient := (-365598270396120912724196589568) }, { argument := 106198891511823567969568423936, coefficient := (-106198891511823567969568423936) }, { argument := 100237832819371243930426277888, coefficient := (-100237832819371243930426277888) }, { argument := 100237967502737048278772219904, coefficient := (-100237967502737048278772219904) }, { argument := 2980372678597041982328012800, coefficient := (-2980372678597041982328012800) }, { argument := 10268770478690638713629704192, coefficient := (-10268770478690638713629704192) }, { argument := 2980813474933753454893465600, coefficient := (-2980813474933753454893465600) }, { argument := 9062781746282126028832768000, coefficient := (-9062781746282126028832768000) }, { argument := 9062794182927461016183767040, coefficient := (-9062794182927461016183767040) }, { argument := 239416646094649553770774528, coefficient := (-239416646094649553770774528) }, { argument := 239417148168883861962358784, coefficient := (-239417148168883861962358784) }, { argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 237684326982332595212694585344, coefficient := 237684326982332595212694585344 }, { argument := 237684648103253430348569116672, coefficient := 237684648103253430348569116672 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 436658291981359785633162199040, coefficient := 436658291981359785633162199040 }, { argument := 1503467854618962790820549230592, coefficient := 1503467854618962790820549230592 }, { argument := 436718728827607551352607080448, coefficient := 436718728827607551352607080448 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 32534639991667797567563890688, coefficient := 32534639991667797567563890688 }, { argument := 1155887552159240157114044252160, coefficient := 1155887552159240157114044252160 }, { argument := 1155962770012579304823008002048, coefficient := 1155962770012579304823008002048 }, { argument := 32459913264442868301702365184, coefficient := 32459913264442868301702365184 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 957799814788587181532250112, coefficient := 957799814788587181532250112 }, { argument := 36250755179634613039835119616, coefficient := 36250755179634613039835119616 }, { argument := 400951600644216584418396995584, coefficient := 400951600644216584418396995584 }, { argument := 36251151858419174090033070080, coefficient := 36251151858419174090033070080 }, { argument := 957667588527066831466266624, coefficient := 957667588527066831466266624 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9
