import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-53455048145170158454024958877106176)
def positiveArguments : Array ℕ := #[
    135, 2565, 3915, 40365, 1215, 3915,
    1215, 1215, 104085, 1215, 40365, 104085,
    135, 1215, 1215, 2565, 105, 1869,
    105, 3325, 5677, 105, 5677, 5677,
    1869, 105, 1, 1, 1399787307, 10137879629,
    2799574365, 216310345, 8038079927, 8037857893, 216532379, 6725927,
    1059036949, 42594076651, 1059036949, 26901201, 810437, 68133435,
    272533683, 3241805, 1435659, 6952949, 1435659
  ]
def positiveCoefficients : Array ℕ := #[
    668487621214105348445527080960, 793829050191750101279063408640, 605816906725282972028758917120, 6246181210719296849537893662720, 752048573865868517001217966080, 605816906725282972028758917120,
    752048573865868517001217966080, 752048573865868517001217966080, 32212747247254701478218836213760, 752048573865868517001217966080, 6246181210719296849537893662720, 32212747247254701478218836213760,
    668487621214105348445527080960, 752048573865868517001217966080, 752048573865868517001217966080, 793829050191750101279063408640, 8123981507810308054025502720, 144606870839023483361653948416,
    8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864, 8123981507810308054025502720, 219618300094471994393822756864, 219618300094471994393822756864,
    144606870839023483361653948416, 8123981507810308054025502720, 633825300114114700748351602688, 633825300114114700748351602688, 13220617323446324611449926713344, 47874782967356553674386030198784,
    13220616147577070376908268503040, 8171973785007756369617443880960, 303670073871136676398571544641536, 303661685663779416568128522420224, 8180361992365016200060466102272, 254098337848223873785749569536,
    40009284736625038654600518828032, 402289679890925893346685398024192, 40009284736625038654600518828032, 254074659902678765384648097792, 122469776808877653057668644864, 10296033593816882740493360824320,
    10296031440417766551935143378944, 122471930207993841615886090240, 13559415884860303955699171328, 131337493258808067275689558016, 13559415884860303955699171328
  ]
def positiveScales : Array ℕ := #[
    7, 11, 11, 15, 10, 11,
    10, 10, 16, 10, 15, 16,
    7, 10, 10, 11, 6, 10,
    6, 11, 12, 6, 12, 12,
    10, 6, 0, 0, 30, 33,
    31, 27, 32, 32, 27, 22,
    29, 35, 29, 24, 19, 26,
    28, 21, 20, 22, 20
  ]
def negativeArguments : Array ℕ := #[
    1429, 135, 7, 1, 469, 123,
    3047, 263, 1
  ]
def negativeCoefficients : Array ℕ := #[
    226434088465767476842348610060288, 85566415515405484601027466362880, 1109194275199700726309615304704, 1267650600228229401496703205376, 74316016438379948662744225415168, 623684095312288865536377977044992,
    482816422361926873295056833347584, 20837006741251520787102058938368, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    10, 7, 2, 0, 8, 6,
    11, 8, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7076815597050830, 11324743110494416, 11934796591681559, 15300817271248935, 10246740598493143, 11934796591681559,
    10246740598493143, 10246740598493143, 16667402646963816, 10246740598493143, 15300817271248935, 16667402646963816,
    7076815597050830, 10246740598493143, 10246740598493143, 11324743110494416, 6714245517659862, 10868050853594526,
    6714245517659862, 11699138625271509, 12470913026274870, 6714245517659862, 12470913026274870, 12470913026274870,
    10868050853594526, 6714245517659862, 0, 0, 30382560485122464, 33239036888334273,
    31382560356806155, 27688527422653837, 32904203776664589, 32904163924887025, 27690007532453620, 22681301689947684,
    29980105777676291, 35309933764761437, 29980105777676291, 24681167247327592, 19628340515428494, 26021859607401120,
    28021859305663706, 21628365882265884, 20453281687963018, 22729193576691355, 20453281687963018
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10480790201095958, 7076815597050831, 2807354922807594, 0, 8873444115207229, 6942514514520450,
    11573173784689130, 8038918989292303, 0
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 249115695057 / 500000000000
noncomputable def negativeCeiling : ℝ := 33045250661 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 226434088465767476842348610060288, coefficient := (-226434088465767476842348610060288) }, { argument := 668487621214105348445527080960, coefficient := 668487621214105348445527080960 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 605816906725282972028758917120, coefficient := 605816906725282972028758917120 }, { argument := 6246181210719296849537893662720, coefficient := 6246181210719296849537893662720 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 605816906725282972028758917120, coefficient := 605816906725282972028758917120 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 32212747247254701478218836213760, coefficient := 32212747247254701478218836213760 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 6246181210719296849537893662720, coefficient := 6246181210719296849537893662720 }, { argument := 32212747247254701478218836213760, coefficient := 32212747247254701478218836213760 }, { argument := 668487621214105348445527080960, coefficient := 668487621214105348445527080960 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 752048573865868517001217966080, coefficient := 752048573865868517001217966080 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 85566415515405484601027466362880, coefficient := (-85566415515405484601027466362880) }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 13220617323446324611449926713344, coefficient := 13220617323446324611449926713344 }, { argument := 47874782967356553674386030198784, coefficient := 47874782967356553674386030198784 }, { argument := 13220616147577070376908268503040, coefficient := 13220616147577070376908268503040 }, { argument := 74316016438379948662744225415168, coefficient := (-74316016438379948662744225415168) }, { argument := 8171973785007756369617443880960, coefficient := 8171973785007756369617443880960 }, { argument := 303670073871136676398571544641536, coefficient := 303670073871136676398571544641536 }, { argument := 303661685663779416568128522420224, coefficient := 303661685663779416568128522420224 }, { argument := 8180361992365016200060466102272, coefficient := 8180361992365016200060466102272 }, { argument := 623684095312288865536377977044992, coefficient := (-623684095312288865536377977044992) }, { argument := 254098337848223873785749569536, coefficient := 254098337848223873785749569536 }, { argument := 40009284736625038654600518828032, coefficient := 40009284736625038654600518828032 }, { argument := 402289679890925893346685398024192, coefficient := 402289679890925893346685398024192 }, { argument := 40009284736625038654600518828032, coefficient := 40009284736625038654600518828032 }, { argument := 254074659902678765384648097792, coefficient := 254074659902678765384648097792 }, { argument := 482816422361926873295056833347584, coefficient := (-482816422361926873295056833347584) }, { argument := 122469776808877653057668644864, coefficient := 122469776808877653057668644864 }, { argument := 10296033593816882740493360824320, coefficient := 10296033593816882740493360824320 }, { argument := 10296031440417766551935143378944, coefficient := 10296031440417766551935143378944 }, { argument := 122471930207993841615886090240, coefficient := 122471930207993841615886090240 }, { argument := 20837006741251520787102058938368, coefficient := (-20837006741251520787102058938368) }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 131337493258808067275689558016, coefficient := 131337493258808067275689558016 }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
