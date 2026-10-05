import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 11, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-141607738292728755579926310027264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17143, 3150903045, 17143, 52535, 155393, 346731,
    17143, 173089, 352261, 17143, 52535, 17143,
    34069, 104405, 308819, 689073, 34069, 343987,
    700063, 34069, 104405, 34069, 51551675, 10224493125,
    10224493125, 51551675, 5425, 16625, 49175, 109725,
    5425, 54775, 111475, 5425, 16625, 5425,
    525791, 1611295, 4766041, 10634547, 525791, 5308793,
    10804157, 525791, 1611295, 525791, 43135075, 8555188125,
    8555188125, 43135075, 33635, 103075, 304885, 680295,
    33635, 339605, 691145, 33635, 103075, 33635,
    1206730025, 239336604375, 239336604375, 1206730025
  ]
def negativeCoefficients : Array ℕ := #[
    161911057231668655796781056, 56761623117370244758241280, 161911057231668655796781056, 3969432370840908980824309760, 2935290779490251114767450112, 3274781705943749909180055552,
    161911057231668655796781056, 3269558768613696081573707776, 3327011079244288185243533312, 161911057231668655796781056, 3969432370840908980824309760, 161911057231668655796781056,
    160886303704885942785409024, 3944309381152042468287447040, 2916712989746641930496770048, 3254055239450435036337143808, 160886303704885942785409024, 3248865358685761296247291904,
    3305954047097172437235662848, 160886303704885942785409024, 3944309381152042468287447040, 160886303704885942785409024, 118870069412006356162969600, 23576075995034725468078080000,
    23576075995034725468078080000, 118870069412006356162969600, 102475352678271301137203200, 2512298968886651253686272000, 1857778974360918427068006400, 2072646649331487284291174400,
    102475352678271301137203200, 2069340992793478532641587200, 2105703214711574800787046400, 102475352678271301137203200, 2512298968886651253686272000, 102475352678271301137203200,
    2482977795394513626554433536, 60873004016123559876818370560, 45013984548765053487857795072, 50220228313301936898375155712, 2482977795394513626554433536, 50140132255385984845905657856,
    51021188892461457423070134272, 2482977795394513626554433536, 60873004016123559876818370560, 2482977795394513626554433536, 1591403378250534074345062400, 315630731688628161368555520000,
    315630731688628161368555520000, 1591403378250534074345062400, 158836796651320516762664960, 3894063401774309443213721600, 2879557410259423561955409920, 3212602306463805290651320320,
    158836796651320516762664960, 3207478538829891725594460160, 3263839982802940941219921920, 158836796651320516762664960, 3894063401774309443213721600, 158836796651320516762664960,
    2782529992154516133039308800, 551872636047037349222154240000, 551872636047037349222154240000, 2782529992154516133039308800
  ]
def negativeScales : Array ℕ := #[
    14, 31, 14, 15, 17, 18,
    14, 17, 18, 14, 15, 14,
    15, 16, 18, 19, 15, 18,
    19, 15, 16, 15, 25, 33,
    33, 25, 12, 14, 15, 16,
    12, 15, 16, 12, 14, 12,
    19, 20, 22, 23, 19, 22,
    23, 19, 20, 19, 25, 32,
    32, 25, 15, 16, 18, 19,
    15, 18, 19, 15, 16, 15,
    30, 37, 37, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14065331980621583, 31553118216515278, 14065331980621583, 15680991278611640, 17245561990455634, 18403457303036754,
    14065331980621583, 17401154517167333, 18426285232491027, 14065331980621583, 15680991278611640, 14065331980621583,
    15056171981336107, 16671831279316955, 18236401991170158, 19394297303751276, 15056171981336107, 18391994517881855,
    19417125233205545, 15056171981336107, 16671831279316955, 15056171981336107, 25619515968146929, 33251310272805963,
    33251310272805963, 25619515968146929, 12405407422219213, 14021066720163277, 15585637432057036, 16743532744829480,
    12405407422219213, 15741229958950381, 16766360674408847, 12405407422219213, 14021066720163277, 12405407422219213,
    19004129921895826, 20619789219849587, 22184359931729877, 23342255244310991, 19004129921895826, 22339952458441570,
    23365083173765253, 19004129921895826, 20619789219849587, 19004129921895826, 25362358128640189, 32994152454870937,
    32994152454870937, 25362358128640189, 15037675637718717, 16653334935685977, 18217905647552768, 19375800960133884,
    15037675637718717, 18373498174264463, 19398628889588149, 15037675637718717, 16653334935685977, 15037675637718717,
    30168455800037929, 37800250105355915, 37800250105355915, 30168455800037929
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
noncomputable def negativeCeiling : ℝ := 175466829 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 56761623117370244758241280, coefficient := (-56761623117370244758241280) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 3944309381152042468287447040, coefficient := (-3944309381152042468287447040) }, { argument := 2916712989746641930496770048, coefficient := (-2916712989746641930496770048) }, { argument := 3254055239450435036337143808, coefficient := (-3254055239450435036337143808) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 3248865358685761296247291904, coefficient := (-3248865358685761296247291904) }, { argument := 3305954047097172437235662848, coefficient := (-3305954047097172437235662848) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 3944309381152042468287447040, coefficient := (-3944309381152042468287447040) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 1857778974360918427068006400, coefficient := (-1857778974360918427068006400) }, { argument := 2072646649331487284291174400, coefficient := (-2072646649331487284291174400) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2069340992793478532641587200, coefficient := (-2069340992793478532641587200) }, { argument := 2105703214711574800787046400, coefficient := (-2105703214711574800787046400) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 60873004016123559876818370560, coefficient := (-60873004016123559876818370560) }, { argument := 45013984548765053487857795072, coefficient := (-45013984548765053487857795072) }, { argument := 50220228313301936898375155712, coefficient := (-50220228313301936898375155712) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 50140132255385984845905657856, coefficient := (-50140132255385984845905657856) }, { argument := 51021188892461457423070134272, coefficient := (-51021188892461457423070134272) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 60873004016123559876818370560, coefficient := (-60873004016123559876818370560) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 2879557410259423561955409920, coefficient := (-2879557410259423561955409920) }, { argument := 3212602306463805290651320320, coefficient := (-3212602306463805290651320320) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3207478538829891725594460160, coefficient := (-3207478538829891725594460160) }, { argument := 3263839982802940941219921920, coefficient := (-3263839982802940941219921920) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }] }

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

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-469333808895504197116200960917504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16293585, 5477726835, 52535, 55667044923, 16625, 1995,
    52535, 104405, 16625, 1611295, 103075, 2738871303,
    52535, 1995, 103075, 1995, 52535, 52535,
    16293585, 134005935, 535630575, 267356595, 535630575, 6515305802691,
    2738871303, 244765672857237, 1154910981, 112996023, 1154830341, 2307951009,
    817524858549, 2738871303, 112996023, 7824517161257, 477204017768151, 3964599375,
    10224493125, 8555188125, 239336604375, 119274309637563, 8555188125, 7720535625,
    3964599375, 3964599375, 7720535625, 239336604375, 7720535625, 1956115214789,
    10224493125, 17143, 52535, 155393, 346731, 17143,
    173089, 352261, 17143, 52535, 17143, 43135075,
    8555188125, 8555188125, 43135075, 123960449763
  ]
def negativeCoefficients : Array ℕ := #[
    300563592538232844567183360, 50523112515468014441390407680, 3969432370840908980824309760, 513437865517136816531029622784, 2512298968886651253686272000, 150737938133199075221176320,
    3969432370840908980824309760, 3944309381152042468287447040, 2512298968886651253686272000, 60873004016123559876818370560, 3894063401774309443213721600, 50523257977268407678059675648,
    3969432370840908980824309760, 150737938133199075221176320, 3894063401774309443213721600, 150737938133199075221176320, 3969432370840908980824309760, 3969432370840908980824309760,
    300563592538232844567183360, 4943946374606314765465681920, 4940320067539444757535129600, 4931858684383414739030507520, 4940320067539444757535129600, 7335582196301004483732701184,
    50523257977268407678059675648, 275581648268235320045378469888, 42608694588847669131809390592, 2084408717627998189721223168, 42605719497963461255324762112, 42574181597682730025084780544,
    7363609296654787702431940608, 50523257977268407678059675648, 2084408717627998189721223168, 35238492571791076361316073472, 2149135836600348395846705872896, 18283487506353460567080960000,
    23576075995034725468078080000, 315630731688628161368555520000, 551872636047037349222154240000, 2148654945754407546449918164992, 315630731688628161368555520000, 17802343098291527394263040000,
    18283487506353460567080960000, 18283487506353460567080960000, 17802343098291527394263040000, 551872636047037349222154240000, 17802343098291527394263040000, 35238239009669992585285861376,
    23576075995034725468078080000, 161911057231668655796781056, 3969432370840908980824309760, 2935290779490251114767450112, 3274781705943749909180055552, 161911057231668655796781056,
    3269558768613696081573707776, 3327011079244288185243533312, 161911057231668655796781056, 3969432370840908980824309760, 161911057231668655796781056, 1591403378250534074345062400,
    315630731688628161368555520000, 315630731688628161368555520000, 1591403378250534074345062400, 2233072941445303556785569792
  ]
def negativeScales : Array ℕ := #[
    23, 32, 15, 35, 14, 10,
    15, 16, 14, 20, 16, 31,
    15, 10, 16, 10, 15, 15,
    23, 26, 28, 27, 28, 42,
    31, 47, 30, 26, 30, 31,
    39, 31, 26, 42, 48, 31,
    33, 32, 37, 46, 32, 32,
    31, 31, 32, 37, 32, 40,
    33, 14, 15, 17, 18, 14,
    17, 18, 14, 15, 14, 25,
    32, 32, 25, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23957800744212914, 32350930177054549, 15680991278611640, 35696104448919241, 14021066720163277, 10962173043893966,
    15680991278611640, 16671831279316955, 14021066720163277, 20619789219849587, 16653334935685977, 31350934330732054,
    15680991278611640, 10962173043893966, 16653334935685977, 10962173043893966, 15680991278611640, 15680991278611640,
    23957800744212914, 26997721679668275, 28996663096842367, 27994190045427910, 28996663096842367, 42566970033433529,
    31350934330732054, 47798394570611582, 30105134508900998, 26751696755874086, 30105033771275501, 31103965454129580,
    39572471643194005, 31350934330732054, 26751696755874086, 42831138868183948, 48761599518412991, 31884527945435175,
    33251310272805963, 32994152454870937, 37800250105355915, 46761276664704667, 32994152454870937, 32846053795925841,
    31884527945435175, 31884527945435175, 32846053795925841, 37800250105355915, 32846053795925841, 40831128487088938,
    33251310272805963, 14065331980621583, 15680991278611640, 17245561990455634, 18403457303036754, 14065331980621583,
    17401154517167333, 18426285232491027, 14065331980621583, 15680991278611640, 14065331980621583, 25362358128640189,
    32994152454870937, 32994152454870937, 25362358128640189, 36851088940074721
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
noncomputable def negativeCeiling : ℝ := 514723703 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 50523112515468014441390407680, coefficient := (-50523112515468014441390407680) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 513437865517136816531029622784, coefficient := (-513437865517136816531029622784) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 3944309381152042468287447040, coefficient := (-3944309381152042468287447040) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 60873004016123559876818370560, coefficient := (-60873004016123559876818370560) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 50523257977268407678059675648, coefficient := (-50523257977268407678059675648) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 4943946374606314765465681920, coefficient := (-4943946374606314765465681920) }, { argument := 4940320067539444757535129600, coefficient := (-4940320067539444757535129600) }, { argument := 4931858684383414739030507520, coefficient := (-4931858684383414739030507520) }, { argument := 4940320067539444757535129600, coefficient := (-4940320067539444757535129600) }, { argument := 7335582196301004483732701184, coefficient := (-7335582196301004483732701184) }, { argument := 50523257977268407678059675648, coefficient := (-50523257977268407678059675648) }, { argument := 275581648268235320045378469888, coefficient := (-275581648268235320045378469888) }, { argument := 42608694588847669131809390592, coefficient := (-42608694588847669131809390592) }, { argument := 2084408717627998189721223168, coefficient := (-2084408717627998189721223168) }, { argument := 42605719497963461255324762112, coefficient := (-42605719497963461255324762112) }, { argument := 42574181597682730025084780544, coefficient := (-42574181597682730025084780544) }, { argument := 7363609296654787702431940608, coefficient := (-7363609296654787702431940608) }, { argument := 50523257977268407678059675648, coefficient := (-50523257977268407678059675648) }, { argument := 2084408717627998189721223168, coefficient := (-2084408717627998189721223168) }, { argument := 35238492571791076361316073472, coefficient := (-35238492571791076361316073472) }, { argument := 2149135836600348395846705872896, coefficient := (-2149135836600348395846705872896) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 2148654945754407546449918164992, coefficient := (-2148654945754407546449918164992) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 35238239009669992585285861376, coefficient := (-35238239009669992585285861376) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 2233072941445303556785569792, coefficient := (-2233072941445303556785569792) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
