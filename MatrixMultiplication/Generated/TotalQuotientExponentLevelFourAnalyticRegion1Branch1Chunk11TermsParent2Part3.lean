import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-140170291506251112922136707072000)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    239336604375, 1206730025, 6793731, 2309654025, 173089, 23497106913,
    54775, 6573, 173089, 343987, 54775, 5308793,
    339605, 1154830341, 173089, 6573, 339605, 6573,
    173089, 173089, 6793731, 38926775, 7720535625, 7720535625,
    38926775, 13694919, 4615888725, 352261, 46920348237, 111475,
    13377, 352261, 700063, 111475, 10804157, 691145,
    2307951009, 352261, 13377, 691145, 13377, 352261,
    352261, 13694919, 4285039475, 83777800265, 167555585155, 535630575,
    3150903045, 16293585, 123960449763, 6799107, 668577, 6793731,
    13694919, 395508291, 16293585, 668577, 66977530071, 7824999200553,
    19989425, 51551675, 43135075, 1206730025
  ]
def negativeCoefficients : Array ℕ := #[
    551872636047037349222154240000, 2782529992154516133039308800, 250644434125253731619438592, 42605596697988162570839654400, 3269558768613696081573707776, 433445117696702486830443921408,
    2069340992793478532641587200, 124160459567608711958495232, 3269558768613696081573707776, 3248865358685761296247291904, 2069340992793478532641587200, 50140132255385984845905657856,
    3207478538829891725594460160, 42605719497963461255324762112, 3269558768613696081573707776, 124160459567608711958495232, 3207478538829891725594460160, 124160459567608711958495232,
    3269558768613696081573707776, 3269558768613696081573707776, 250644434125253731619438592, 89759032004984391388364800, 17802343098291527394263040000, 17802343098291527394263040000,
    89759032004984391388364800, 252626665903182338907439104, 42574058991398244114549964800, 3327011079244288185243533312, 432763827888634079107923050496, 2105703214711574800787046400,
    126342192882694488047222784, 3327011079244288185243533312, 3305954047097172437235662848, 2105703214711574800787046400, 51021188892461457423070134272, 3263839982802940941219921920,
    42574181597682730025084780544, 3327011079244288185243533312, 126342192882694488047222784, 3263839982802940941219921920, 126342192882694488047222784, 3327011079244288185243533312,
    3327011079244288185243533312, 252626665903182338907439104, 4940314158816733647444377600, 193178455068351406613494497280, 193178437342183273283222241280, 4940320067539444757535129600,
    56761623117370244758241280, 300563592538232844567183360, 2233072941445303556785569792, 250842773517534256718413824, 12333068812568510890770432, 250644434125253731619438592,
    252626665903182338907439104, 56998751743025334297034752, 300563592538232844567183360, 12333068812568510890770432, 301639979469951790498185216, 35240663483784919897539084288,
    92184951788902888452915200, 118870069412006356162969600, 1591403378250534074345062400, 2782529992154516133039308800
  ]
def negativeScales : Array ℕ := #[
    37, 30, 22, 31, 17, 34,
    15, 12, 17, 18, 15, 22,
    18, 30, 17, 12, 18, 12,
    17, 17, 22, 25, 32, 32,
    25, 23, 32, 18, 35, 16,
    13, 18, 19, 16, 23, 19,
    31, 18, 13, 19, 13, 18,
    18, 23, 31, 36, 37, 28,
    31, 23, 36, 22, 19, 22,
    23, 28, 23, 19, 35, 42,
    24, 25, 25, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37800250105355915, 30168455800037929, 22695772664755894, 31105029613073908, 17401154517167333, 34451764084420975,
    15741229958950381, 12682336269758884, 17401154517167333, 18391994517881855, 15741229958950381, 22339952458441570,
    18373498174264463, 30105033771275501, 17401154517167333, 12682336269758884, 18373498174264463, 12682336269758884,
    17401154517167333, 17401154517167333, 22695772664755894, 25214259489651054, 32846053795925841, 32846053795925841,
    25214259489651054, 23707137397398138, 32103961299411235, 18426285232491027, 35449494669783326, 16766360674408847,
    13707466985121264, 18426285232491027, 19417125233205545, 16766360674408847, 23365083173765253, 19398628889588149,
    31103965454129580, 18426285232491027, 13707466985121264, 19398628889588149, 13707466985121264, 18426285232491027,
    18426285232491027, 23707137397398138, 31996661371348270, 36285848953053723, 37285848820671176, 28996663096842367,
    31553118216515278, 23957800744212914, 36851088940074721, 22696913843508470, 19350734199483832, 22695772664755894,
    23707137397398138, 28559132697184836, 23957800744212914, 19350734199483832, 35962958136616192, 42831227744504771,
    24252733637465689, 25619515968146929, 25362358128640189, 30168455800037929
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
noncomputable def negativeCeiling : ℝ := 931840597 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 250644434125253731619438592, coefficient := (-250644434125253731619438592) }, { argument := 42605596697988162570839654400, coefficient := (-42605596697988162570839654400) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 433445117696702486830443921408, coefficient := (-433445117696702486830443921408) }, { argument := 2069340992793478532641587200, coefficient := (-2069340992793478532641587200) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3248865358685761296247291904, coefficient := (-3248865358685761296247291904) }, { argument := 2069340992793478532641587200, coefficient := (-2069340992793478532641587200) }, { argument := 50140132255385984845905657856, coefficient := (-50140132255385984845905657856) }, { argument := 3207478538829891725594460160, coefficient := (-3207478538829891725594460160) }, { argument := 42605719497963461255324762112, coefficient := (-42605719497963461255324762112) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3207478538829891725594460160, coefficient := (-3207478538829891725594460160) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 250644434125253731619438592, coefficient := (-250644434125253731619438592) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 252626665903182338907439104, coefficient := (-252626665903182338907439104) }, { argument := 42574058991398244114549964800, coefficient := (-42574058991398244114549964800) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 432763827888634079107923050496, coefficient := (-432763827888634079107923050496) }, { argument := 2105703214711574800787046400, coefficient := (-2105703214711574800787046400) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 3305954047097172437235662848, coefficient := (-3305954047097172437235662848) }, { argument := 2105703214711574800787046400, coefficient := (-2105703214711574800787046400) }, { argument := 51021188892461457423070134272, coefficient := (-51021188892461457423070134272) }, { argument := 3263839982802940941219921920, coefficient := (-3263839982802940941219921920) }, { argument := 42574181597682730025084780544, coefficient := (-42574181597682730025084780544) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 3263839982802940941219921920, coefficient := (-3263839982802940941219921920) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 252626665903182338907439104, coefficient := (-252626665903182338907439104) }, { argument := 4940314158816733647444377600, coefficient := (-4940314158816733647444377600) }, { argument := 193178455068351406613494497280, coefficient := (-193178455068351406613494497280) }, { argument := 193178437342183273283222241280, coefficient := (-193178437342183273283222241280) }, { argument := 4940320067539444757535129600, coefficient := (-4940320067539444757535129600) }, { argument := 56761623117370244758241280, coefficient := (-56761623117370244758241280) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 2233072941445303556785569792, coefficient := (-2233072941445303556785569792) }, { argument := 250842773517534256718413824, coefficient := (-250842773517534256718413824) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 250644434125253731619438592, coefficient := (-250644434125253731619438592) }, { argument := 252626665903182338907439104, coefficient := (-252626665903182338907439104) }, { argument := 56998751743025334297034752, coefficient := (-56998751743025334297034752) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 301639979469951790498185216, coefficient := (-301639979469951790498185216) }, { argument := 35240663483784919897539084288, coefficient := (-35240663483784919897539084288) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }] }

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

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-82011281958621343359063036002304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1956115214789, 43135075, 38926775, 19989425, 19989425, 38926775,
    1206730025, 38926775, 16744302267, 51551675, 395508291, 204380947485,
    17143, 7915034527863, 5425, 651, 17143, 34069,
    5425, 525791, 33635, 817524858549, 17143, 651,
    33635, 651, 17143, 17143, 395508291, 51551675,
    10224493125, 10224493125, 51551675, 16293585, 5477726835, 52535,
    55667044923, 16625, 1995, 52535, 104405, 16625,
    1611295, 103075, 2738871303, 52535, 1995, 103075,
    1995, 52535, 52535, 16293585, 2138850215, 41817334565,
    83634661495, 267356595, 668577, 225991395, 17143, 2297832747,
    5425, 651, 17143, 34069
  ]
def negativeCoefficients : Array ℕ := #[
    35238239009669992585285861376, 1591403378250534074345062400, 89759032004984391388364800, 92184951788902888452915200, 92184951788902888452915200, 89759032004984391388364800,
    2782529992154516133039308800, 89759032004984391388364800, 301638533800960605686857728, 118870069412006356162969600, 56998751743025334297034752, 7363599671480599292915220480,
    161911057231668655796781056, 71292293100616833079072260096, 102475352678271301137203200, 6148521160696278068232192, 161911057231668655796781056, 160886303704885942785409024,
    102475352678271301137203200, 2482977795394513626554433536, 158836796651320516762664960, 7363609296654787702431940608, 161911057231668655796781056, 6148521160696278068232192,
    158836796651320516762664960, 6148521160696278068232192, 161911057231668655796781056, 161911057231668655796781056, 56998751743025334297034752, 118870069412006356162969600,
    23576075995034725468078080000, 23576075995034725468078080000, 118870069412006356162969600, 300563592538232844567183360, 50523112515468014441390407680, 3969432370840908980824309760,
    513437865517136816531029622784, 2512298968886651253686272000, 150737938133199075221176320, 3969432370840908980824309760, 3944309381152042468287447040, 2512298968886651253686272000,
    60873004016123559876818370560, 3894063401774309443213721600, 50523257977268407678059675648, 3969432370840908980824309760, 150737938133199075221176320, 3894063401774309443213721600,
    150737938133199075221176320, 3969432370840908980824309760, 3969432370840908980824309760, 300563592538232844567183360, 4931852816012956290179399680, 192848417141310835140602101760,
    192848399536199459794048778240, 4931858684383414739030507520, 12333068812568510890770432, 2084402713212802197262172160, 161911057231668655796781056, 21193766304048994734965784576,
    102475352678271301137203200, 6148521160696278068232192, 161911057231668655796781056, 160886303704885942785409024
  ]
def negativeScales : Array ℕ := #[
    40, 25, 25, 24, 24, 25,
    30, 25, 33, 25, 28, 37,
    14, 42, 12, 9, 14, 15,
    12, 19, 15, 39, 14, 9,
    15, 9, 14, 14, 28, 25,
    33, 33, 25, 23, 32, 15,
    35, 14, 10, 15, 16, 14,
    20, 16, 31, 15, 10, 16,
    10, 15, 15, 23, 30, 35,
    36, 27, 19, 27, 14, 31,
    12, 9, 14, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    40831128487088938, 25362358128640189, 25214259489651054, 24252733637465689, 24252733637465689, 25214259489651054,
    30168455800037929, 25214259489651054, 33962951222198099, 25619515968146929, 28559132697184836, 37572469757406806,
    14065331980621583, 42847732784171430, 12405407422219213, 9346513733165637, 14065331980621583, 15056171981336107,
    12405407422219213, 19004129921895826, 15037675637718717, 39572471643194005, 14065331980621583, 9346513733165637,
    15037675637718717, 9346513733165637, 14065331980621583, 14065331980621583, 28559132697184836, 25619515968146929,
    33251310272805963, 33251310272805963, 25619515968146929, 23957800744212914, 32350930177054549, 15680991278611640,
    35696104448919241, 14021066720163277, 10962173043893966, 15680991278611640, 16671831279316955, 14021066720163277,
    20619789219849587, 16653334935685977, 31350934330732054, 15680991278611640, 10962173043893966, 16653334935685977,
    10962173043893966, 15680991278611640, 15680991278611640, 23957800744212914, 30994188328777562, 35283382056415491,
    36283381924712009, 27994190045427910, 19350734199483832, 27751692599994064, 14065331980621583, 31097626645941103,
    12405407422219213, 9346513733165637, 14065331980621583, 15056171981336107
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
noncomputable def negativeCeiling : ℝ := 67816677 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35238239009669992585285861376, coefficient := (-35238239009669992585285861376) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 301638533800960605686857728, coefficient := (-301638533800960605686857728) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 56998751743025334297034752, coefficient := (-56998751743025334297034752) }, { argument := 7363599671480599292915220480, coefficient := (-7363599671480599292915220480) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 71292293100616833079072260096, coefficient := (-71292293100616833079072260096) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 7363609296654787702431940608, coefficient := (-7363609296654787702431940608) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 56998751743025334297034752, coefficient := (-56998751743025334297034752) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 50523112515468014441390407680, coefficient := (-50523112515468014441390407680) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 513437865517136816531029622784, coefficient := (-513437865517136816531029622784) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 3944309381152042468287447040, coefficient := (-3944309381152042468287447040) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 60873004016123559876818370560, coefficient := (-60873004016123559876818370560) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 50523257977268407678059675648, coefficient := (-50523257977268407678059675648) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 4931852816012956290179399680, coefficient := (-4931852816012956290179399680) }, { argument := 192848417141310835140602101760, coefficient := (-192848417141310835140602101760) }, { argument := 192848399536199459794048778240, coefficient := (-192848399536199459794048778240) }, { argument := 4931858684383414739030507520, coefficient := (-4931858684383414739030507520) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 2084402713212802197262172160, coefficient := (-2084402713212802197262172160) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 21193766304048994734965784576, coefficient := (-21193766304048994734965784576) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
