import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 24, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24

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
def constantNumerator : ℤ := (-62963628193202770424816480550912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3849, 1185687, 79, 41533989, 25, 3,
    79, 157, 25, 2423, 155, 4742751,
    79, 3, 155, 3, 79, 79,
    3849, 139452007, 41, 1280840037, 429, 19,
    2561679159, 19, 37, 699, 37, 429,
    699, 17431539, 37, 37, 41, 4544897,
    22724485, 18828859, 3237371753, 126607845, 290873359, 507080651,
    507080651, 362942489, 18828859, 70245145, 1369969435, 2739937865,
    8780685, 22724485, 2656051125, 727183275, 139452007, 70245145,
    139452007, 70245145, 18828859, 2200728075, 602523285, 41,
    41, 3849, 139452007, 41
  ]
def negativeCoefficients : Array ℕ := #[
    290822217481044230840254464, 22396994191897044097966276608, 3056164471985782553657212928, 196138717553476532739552313344, 1934281311383406679529881600, 116056878683004400771792896,
    3056164471985782553657212928, 3036821658871948486861914112, 1934281311383406679529881600, 46867636174819943845009031168, 2998136032644280353271316480, 22397008358996492706901917696,
    3056164471985782553657212928, 116056878683004400771792896, 2998136032644280353271316480, 116056878683004400771792896, 3056164471985782553657212928, 3056164471985782553657212928,
    290822217481044230840254464, 2572435483694152907921293312, 1586110675334393477214502912, 47254656723799345638181699584, 16596133651669629310366384128, 1470053796651389076442710016,
    47254639845028518193941970944, 1470053796651389076442710016, 1431368170423720942852112384, 54082505466280050759655489536, 1431368170423720942852112384, 16596133651669629310366384128,
    54082505466280050759655489536, 2572441109951095389334536192, 1431368170423720942852112384, 1431368170423720942852112384, 1586110675334393477214502912, 1341416828805925120174456832,
    13414168288059251201744568320, 694662286345925508661772288, 14929742049761863081983475712, 18684020115511099888144220160, 1341416602833310217232449536, 18707973987454062836718764032,
    18707973987454062836718764032, 13390214416116288253170024448, 694662286345925508661772288, 1295794212235618141150904320, 50542951112498945562949713920, 50542932573521151484850339840,
    1295800391894882833850695680, 13414168288059251201744568320, 48995495349563337492922368000, 13414163768606953142904422400, 2572435483694152907921293312, 1295794212235618141150904320,
    2572435483694152907921293312, 1295794212235618141150904320, 694662286345925508661772288, 2537266723459529977312051200, 694662052302860073471836160, 1586110675334393477214502912,
    1586110675334393477214502912, 290822217481044230840254464, 2572435483694152907921293312, 1586110675334393477214502912
  ]
def negativeScales : Array ℕ := #[
    11, 20, 6, 25, 4, 1,
    6, 7, 4, 11, 7, 22,
    6, 1, 7, 1, 6, 6,
    11, 27, 5, 30, 8, 4,
    31, 4, 5, 9, 5, 8,
    9, 24, 5, 5, 5, 22,
    24, 24, 31, 26, 28, 28,
    28, 28, 24, 26, 30, 31,
    23, 24, 31, 29, 27, 26,
    27, 26, 24, 31, 29, 5,
    5, 11, 27, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11910267961055196, 20177291783976326, 6303780748177104, 25307789101689468, 4643856189792934, 1584962500724866,
    6303780748177104, 7294620748891628, 4643856189792934, 11242578689451347, 7276124405274238, 22177292696545105,
    6303780748177104, 1584962500724866, 7276124405274238, 1584962500724866, 6303780748177104, 6303780748177104,
    11910267961055196, 27055193456951040, 5357552004618085, 30254443163985066, 8744833837700333, 4247927513443586,
    31254442648672397, 4247927513443586, 5209453365628950, 9449148645375482, 5209453365628950, 8744833837700333,
    9449148645375482, 24055196612312628, 5209453365628950, 5209453365628950, 5357552004618085, 22115816168633983,
    24437744263521374, 24166442241703951, 31592175896218378, 26915791566107251, 28115815925600206, 28917639990690431,
    28917639990690431, 28435165719419595, 24166442241703951, 26065895180983267, 30351496559970731, 31351496030795136,
    23065902061198067, 24437744263521374, 31306635770653817, 29437743777453779, 27055193456951040, 26065895180983267,
    27055193456951040, 26065895180983267, 24166442241703951, 31035333748836422, 29166441755636356, 5357552004618085,
    5357552004618085, 11910267961055196, 27055193456951040, 5357552004618085
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 23788447 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 290822217481044230840254464, coefficient := (-290822217481044230840254464) }, { argument := 22396994191897044097966276608, coefficient := (-22396994191897044097966276608) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 196138717553476532739552313344, coefficient := (-196138717553476532739552313344) }, { argument := 1934281311383406679529881600, coefficient := (-1934281311383406679529881600) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 3036821658871948486861914112, coefficient := (-3036821658871948486861914112) }, { argument := 1934281311383406679529881600, coefficient := (-1934281311383406679529881600) }, { argument := 46867636174819943845009031168, coefficient := (-46867636174819943845009031168) }, { argument := 2998136032644280353271316480, coefficient := (-2998136032644280353271316480) }, { argument := 22397008358996492706901917696, coefficient := (-22397008358996492706901917696) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 2998136032644280353271316480, coefficient := (-2998136032644280353271316480) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 290822217481044230840254464, coefficient := (-290822217481044230840254464) }, { argument := 2572435483694152907921293312, coefficient := (-2572435483694152907921293312) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 47254656723799345638181699584, coefficient := (-47254656723799345638181699584) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 47254639845028518193941970944, coefficient := (-47254639845028518193941970944) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 2572441109951095389334536192, coefficient := (-2572441109951095389334536192) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 1341416828805925120174456832, coefficient := (-1341416828805925120174456832) }, { argument := 13414168288059251201744568320, coefficient := (-13414168288059251201744568320) }, { argument := 694662286345925508661772288, coefficient := (-694662286345925508661772288) }, { argument := 14929742049761863081983475712, coefficient := (-14929742049761863081983475712) }, { argument := 18684020115511099888144220160, coefficient := (-18684020115511099888144220160) }, { argument := 1341416602833310217232449536, coefficient := (-1341416602833310217232449536) }, { argument := 18707973987454062836718764032, coefficient := (-18707973987454062836718764032) }, { argument := 18707973987454062836718764032, coefficient := (-18707973987454062836718764032) }, { argument := 13390214416116288253170024448, coefficient := (-13390214416116288253170024448) }, { argument := 694662286345925508661772288, coefficient := (-694662286345925508661772288) }, { argument := 1295794212235618141150904320, coefficient := (-1295794212235618141150904320) }, { argument := 50542951112498945562949713920, coefficient := (-50542951112498945562949713920) }, { argument := 50542932573521151484850339840, coefficient := (-50542932573521151484850339840) }, { argument := 1295800391894882833850695680, coefficient := (-1295800391894882833850695680) }, { argument := 13414168288059251201744568320, coefficient := (-13414168288059251201744568320) }, { argument := 48995495349563337492922368000, coefficient := (-48995495349563337492922368000) }, { argument := 13414163768606953142904422400, coefficient := (-13414163768606953142904422400) }, { argument := 2572435483694152907921293312, coefficient := (-2572435483694152907921293312) }, { argument := 1295794212235618141150904320, coefficient := (-1295794212235618141150904320) }, { argument := 2572435483694152907921293312, coefficient := (-2572435483694152907921293312) }, { argument := 1295794212235618141150904320, coefficient := (-1295794212235618141150904320) }, { argument := 694662286345925508661772288, coefficient := (-694662286345925508661772288) }, { argument := 2537266723459529977312051200, coefficient := (-2537266723459529977312051200) }, { argument := 694662052302860073471836160, coefficient := (-694662052302860073471836160) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 290822217481044230840254464, coefficient := (-290822217481044230840254464) }, { argument := 2572435483694152907921293312, coefficient := (-2572435483694152907921293312) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-116331634163455610378826490576896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1280840037, 429, 19, 2561679159, 19, 37,
    699, 37, 429, 699, 17431539, 37,
    37, 41, 3237371753, 2656051125, 2200728075, 39537218175,
    14797999125, 12949483365, 59267883675, 59267883675, 42420930825, 2200728075,
    1280840037, 1369969435, 1280840037, 1369969435, 126607845, 14797999125,
    4051449675, 429, 429, 1185687, 19, 19,
    79, 290873359, 727183275, 602523285, 12949483365, 4051449675,
    145436655, 16226575365, 16226575365, 11614155735, 602523285, 2561679159,
    2739937865, 2561679159, 2739937865, 41533989, 19, 19,
    25, 3, 70245145, 1369969435, 2739937865, 8780685,
    507080651, 59267883675, 16226575365, 37
  ]
def negativeCoefficients : Array ℕ := #[
    47254656723799345638181699584, 16596133651669629310366384128, 1470053796651389076442710016, 47254639845028518193941970944, 1470053796651389076442710016, 1431368170423720942852112384,
    54082505466280050759655489536, 1431368170423720942852112384, 16596133651669629310366384128, 54082505466280050759655489536, 2572441109951095389334536192, 1431368170423720942852112384,
    1431368170423720942852112384, 1586110675334393477214502912, 14929742049761863081983475712, 48995495349563337492922368000, 2537266723459529977312051200, 91166618132580352977901977600,
    68243725665463220079427584000, 14929737845057135780812554240, 68331217621444583182093516800, 68331217621444583182093516800, 48908003393581974390256435200, 2537266723459529977312051200,
    47254656723799345638181699584, 50542951112498945562949713920, 47254656723799345638181699584, 50542951112498945562949713920, 18684020115511099888144220160, 68243725665463220079427584000,
    18684013820559684734759731200, 16596133651669629310366384128, 16596133651669629310366384128, 22396994191897044097966276608, 1470053796651389076442710016, 1470053796651389076442710016,
    3056164471985782553657212928, 1341416602833310217232449536, 13414163768606953142904422400, 694662052302860073471836160, 14929737845057135780812554240, 18684013820559684734759731200,
    1341416376860695314290442240, 18707967684432197151086346240, 18707967684432197151086346240, 13390209904734440726577807360, 694662052302860073471836160, 47254639845028518193941970944,
    50542932573521151484850339840, 47254639845028518193941970944, 50542932573521151484850339840, 196138717553476532739552313344, 1470053796651389076442710016, 1470053796651389076442710016,
    1934281311383406679529881600, 116056878683004400771792896, 1295794212235618141150904320, 50542951112498945562949713920, 50542932573521151484850339840, 1295800391894882833850695680,
    18707973987454062836718764032, 68331217621444583182093516800, 18707967684432197151086346240, 1431368170423720942852112384
  ]
def negativeScales : Array ℕ := #[
    30, 8, 4, 31, 4, 5,
    9, 5, 8, 9, 24, 5,
    5, 5, 31, 31, 31, 35,
    33, 33, 35, 35, 35, 31,
    30, 30, 30, 30, 26, 33,
    31, 8, 8, 20, 4, 4,
    6, 28, 29, 29, 33, 31,
    27, 33, 33, 33, 29, 31,
    31, 31, 31, 25, 4, 4,
    4, 1, 26, 30, 31, 23,
    28, 35, 33, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30254443163985066, 8744833837700333, 4247927513443586, 31254442648672397, 4247927513443586, 5209453365628950,
    9449148645375482, 5209453365628950, 8744833837700333, 9449148645375482, 24055196612312628, 5209453365628950,
    5209453365628950, 5357552004618085, 31592175896218378, 31306635770653817, 31035333748836422, 35202492315987359,
    33784683067929671, 33592175489908108, 35786531492340501, 35786531492340501, 35304057226552041, 31035333748836422,
    30254443163985066, 30351496559970731, 30254443163985066, 30351496559970731, 26915791566107251, 33784683067929671,
    31915791080039607, 8744833837700333, 8744833837700333, 20177291783976326, 4247927513443586, 4247927513443586,
    6303780748177104, 28115815925600206, 29437743777453779, 29166441755636356, 33592175489908108, 31915791080039607,
    27115815682566388, 33917639504622786, 33917639504622786, 33435165233352000, 29166441755636356, 31254442648672397,
    31351496030795136, 31254442648672397, 31351496030795136, 25307789101689468, 4247927513443586, 4247927513443586,
    4643856189792934, 1584962500724866, 26065895180983267, 30351496559970731, 31351496030795136, 23065902061198067,
    28917639990690431, 35786531492340501, 33917639504622786, 5209453365628950
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 607604209 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 47254656723799345638181699584, coefficient := (-47254656723799345638181699584) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 47254639845028518193941970944, coefficient := (-47254639845028518193941970944) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 54082505466280050759655489536, coefficient := (-54082505466280050759655489536) }, { argument := 2572441109951095389334536192, coefficient := (-2572441109951095389334536192) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1586110675334393477214502912, coefficient := (-1586110675334393477214502912) }, { argument := 14929742049761863081983475712, coefficient := (-14929742049761863081983475712) }, { argument := 48995495349563337492922368000, coefficient := (-48995495349563337492922368000) }, { argument := 2537266723459529977312051200, coefficient := (-2537266723459529977312051200) }, { argument := 91166618132580352977901977600, coefficient := (-91166618132580352977901977600) }, { argument := 68243725665463220079427584000, coefficient := (-68243725665463220079427584000) }, { argument := 14929737845057135780812554240, coefficient := (-14929737845057135780812554240) }, { argument := 68331217621444583182093516800, coefficient := (-68331217621444583182093516800) }, { argument := 68331217621444583182093516800, coefficient := (-68331217621444583182093516800) }, { argument := 48908003393581974390256435200, coefficient := (-48908003393581974390256435200) }, { argument := 2537266723459529977312051200, coefficient := (-2537266723459529977312051200) }, { argument := 47254656723799345638181699584, coefficient := (-47254656723799345638181699584) }, { argument := 50542951112498945562949713920, coefficient := (-50542951112498945562949713920) }, { argument := 47254656723799345638181699584, coefficient := (-47254656723799345638181699584) }, { argument := 50542951112498945562949713920, coefficient := (-50542951112498945562949713920) }, { argument := 18684020115511099888144220160, coefficient := (-18684020115511099888144220160) }, { argument := 68243725665463220079427584000, coefficient := (-68243725665463220079427584000) }, { argument := 18684013820559684734759731200, coefficient := (-18684013820559684734759731200) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 16596133651669629310366384128, coefficient := (-16596133651669629310366384128) }, { argument := 22396994191897044097966276608, coefficient := (-22396994191897044097966276608) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 3056164471985782553657212928, coefficient := (-3056164471985782553657212928) }, { argument := 1341416602833310217232449536, coefficient := (-1341416602833310217232449536) }, { argument := 13414163768606953142904422400, coefficient := (-13414163768606953142904422400) }, { argument := 694662052302860073471836160, coefficient := (-694662052302860073471836160) }, { argument := 14929737845057135780812554240, coefficient := (-14929737845057135780812554240) }, { argument := 18684013820559684734759731200, coefficient := (-18684013820559684734759731200) }, { argument := 1341416376860695314290442240, coefficient := (-1341416376860695314290442240) }, { argument := 18707967684432197151086346240, coefficient := (-18707967684432197151086346240) }, { argument := 18707967684432197151086346240, coefficient := (-18707967684432197151086346240) }, { argument := 13390209904734440726577807360, coefficient := (-13390209904734440726577807360) }, { argument := 694662052302860073471836160, coefficient := (-694662052302860073471836160) }, { argument := 47254639845028518193941970944, coefficient := (-47254639845028518193941970944) }, { argument := 50542932573521151484850339840, coefficient := (-50542932573521151484850339840) }, { argument := 47254639845028518193941970944, coefficient := (-47254639845028518193941970944) }, { argument := 50542932573521151484850339840, coefficient := (-50542932573521151484850339840) }, { argument := 196138717553476532739552313344, coefficient := (-196138717553476532739552313344) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1934281311383406679529881600, coefficient := (-1934281311383406679529881600) }, { argument := 116056878683004400771792896, coefficient := (-116056878683004400771792896) }, { argument := 1295794212235618141150904320, coefficient := (-1295794212235618141150904320) }, { argument := 50542951112498945562949713920, coefficient := (-50542951112498945562949713920) }, { argument := 50542932573521151484850339840, coefficient := (-50542932573521151484850339840) }, { argument := 1295800391894882833850695680, coefficient := (-1295800391894882833850695680) }, { argument := 18707973987454062836718764032, coefficient := (-18707973987454062836718764032) }, { argument := 68331217621444583182093516800, coefficient := (-68331217621444583182093516800) }, { argument := 18707967684432197151086346240, coefficient := (-18707967684432197151086346240) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }] }

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

end TermShard1


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24
