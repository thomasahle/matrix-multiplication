import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-328301104580232806668369689313280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14987765, 1072046195, 4285039475, 2138850215, 4285039475, 3150903045,
    16293585, 123960449763, 6799107, 668577, 6793731, 13694919,
    395508291, 16293585, 668577, 53910545, 20959785545, 83777800265,
    41817334565, 83777800265, 1628824317723, 5477726835, 61191357597693, 2309815305,
    225991395, 2309654025, 4615888725, 204380947485, 5477726835, 225991395,
    17143, 52535, 155393, 346731, 17143, 173089,
    352261, 17143, 52535, 17143, 267911404323, 31300222010589,
    19989425, 51551675, 43135075, 1206730025, 7824517161257, 43135075,
    38926775, 19989425, 19989425, 38926775, 1206730025, 38926775,
    66977530071, 51551675, 7493885, 41919567235, 167555585155, 83634661495,
    167555585155, 63084046153521, 55667044923, 2345987954746647
  ]
def negativeCoefficients : Array ℕ := #[
    70777719089126768096250429440, 4943940448589781086272225280, 4940314158816733647444377600, 4931852816012956290179399680, 4940314158816733647444377600, 56761623117370244758241280,
    300563592538232844567183360, 2233072941445303556785569792, 250842773517534256718413824, 12333068812568510890770432, 250644434125253731619438592, 252626665903182338907439104,
    56998751743025334297034752, 300563592538232844567183360, 12333068812568510890770432, 254585350781235737426992824320, 193319899894225937244734095360, 193178455068351406613494497280,
    192848417141310835140602101760, 193178455068351406613494497280, 7335572590349305183740100608, 50523112515468014441390407680, 275581375275264964085025865728, 42608571788872370447324282880,
    2084402713212802197262172160, 42605596697988162570839654400, 42574058991398244114549964800, 7363599671480599292915220480, 50523112515468014441390407680, 2084402713212802197262172160,
    161911057231668655796781056, 3969432370840908980824309760, 2935290779490251114767450112, 3274781705943749909180055552, 161911057231668655796781056, 3269558768613696081573707776,
    3327011079244288185243533312, 161911057231668655796781056, 3969432370840908980824309760, 161911057231668655796781056, 301641425169342272794263552, 35240917045875604376084545536,
    92184951788902888452915200, 118870069412006356162969600, 1591403378250534074345062400, 2782529992154516133039308800, 35238492571791076361316073472, 1591403378250534074345062400,
    89759032004984391388364800, 92184951788902888452915200, 92184951788902888452915200, 89759032004984391388364800, 2782529992154516133039308800, 89759032004984391388364800,
    301639979469951790498185216, 118870069412006356162969600, 70777742700959182444476497920, 193319882116176336207153725440, 193178437342183273283222241280, 192848399536199459794048778240,
    193178437342183273283222241280, 71026321687505086775090479104, 513437865517136816531029622784, 2641347619703167865495620681728
  ]
def negativeScales : Array ℕ := #[
    23, 29, 31, 30, 31, 31,
    23, 36, 22, 19, 22, 23,
    28, 23, 19, 25, 34, 36,
    35, 36, 40, 32, 45, 31,
    27, 31, 32, 37, 32, 27,
    14, 15, 17, 18, 14, 17,
    18, 14, 15, 14, 37, 44,
    24, 25, 25, 30, 42, 25,
    25, 24, 24, 25, 30, 25,
    35, 25, 22, 35, 37, 36,
    37, 45, 35, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23837281927851364, 29997719950393266, 31996661371348270, 30994188328777562, 31996661371348270, 31553118216515278,
    23957800744212914, 36851088940074721, 22696913843508470, 19350734199483832, 22695772664755894, 23707137397398138,
    28559132697184836, 23957800744212914, 19350734199483832, 25684064158597707, 34286904904549188, 36285848953053723,
    35283382056415491, 36285848953053723, 40566968144221795, 32350930177054549, 45798393141467780, 31105130350989745,
    27751692599994064, 31105029613073908, 32103961299411235, 37572469757406806, 32350930177054549, 27751692599994064,
    14065331980621583, 15680991278611640, 17245561990455634, 18403457303036754, 14065331980621583, 17401154517167333,
    18426285232491027, 14065331980621583, 15680991278611640, 14065331980621583, 37962965051146541, 44831238124884345,
    24252733637465689, 25619515968146929, 25362358128640189, 30168455800037929, 42831138868183948, 25362358128640189,
    25214259489651054, 24252733637465689, 24252733637465689, 25214259489651054, 30168455800037929, 25214259489651054,
    35962958136616192, 25619515968146929, 22837282409142216, 35286904771876322, 37285848820671176, 36283381924712009,
    37285848820671176, 45842340431279004, 35696104448919241, 51059117029314585
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
noncomputable def negativeCeiling : ℝ := 2973666041 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70777719089126768096250429440, coefficient := (-70777719089126768096250429440) }, { argument := 4943940448589781086272225280, coefficient := (-4943940448589781086272225280) }, { argument := 4940314158816733647444377600, coefficient := (-4940314158816733647444377600) }, { argument := 4931852816012956290179399680, coefficient := (-4931852816012956290179399680) }, { argument := 4940314158816733647444377600, coefficient := (-4940314158816733647444377600) }, { argument := 56761623117370244758241280, coefficient := (-56761623117370244758241280) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 2233072941445303556785569792, coefficient := (-2233072941445303556785569792) }, { argument := 250842773517534256718413824, coefficient := (-250842773517534256718413824) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 250644434125253731619438592, coefficient := (-250644434125253731619438592) }, { argument := 252626665903182338907439104, coefficient := (-252626665903182338907439104) }, { argument := 56998751743025334297034752, coefficient := (-56998751743025334297034752) }, { argument := 300563592538232844567183360, coefficient := (-300563592538232844567183360) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 254585350781235737426992824320, coefficient := (-254585350781235737426992824320) }, { argument := 193319899894225937244734095360, coefficient := (-193319899894225937244734095360) }, { argument := 193178455068351406613494497280, coefficient := (-193178455068351406613494497280) }, { argument := 192848417141310835140602101760, coefficient := (-192848417141310835140602101760) }, { argument := 193178455068351406613494497280, coefficient := (-193178455068351406613494497280) }, { argument := 7335572590349305183740100608, coefficient := (-7335572590349305183740100608) }, { argument := 50523112515468014441390407680, coefficient := (-50523112515468014441390407680) }, { argument := 275581375275264964085025865728, coefficient := (-275581375275264964085025865728) }, { argument := 42608571788872370447324282880, coefficient := (-42608571788872370447324282880) }, { argument := 2084402713212802197262172160, coefficient := (-2084402713212802197262172160) }, { argument := 42605596697988162570839654400, coefficient := (-42605596697988162570839654400) }, { argument := 42574058991398244114549964800, coefficient := (-42574058991398244114549964800) }, { argument := 7363599671480599292915220480, coefficient := (-7363599671480599292915220480) }, { argument := 50523112515468014441390407680, coefficient := (-50523112515468014441390407680) }, { argument := 2084402713212802197262172160, coefficient := (-2084402713212802197262172160) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 301641425169342272794263552, coefficient := (-301641425169342272794263552) }, { argument := 35240917045875604376084545536, coefficient := (-35240917045875604376084545536) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 35238492571791076361316073472, coefficient := (-35238492571791076361316073472) }, { argument := 1591403378250534074345062400, coefficient := (-1591403378250534074345062400) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 301639979469951790498185216, coefficient := (-301639979469951790498185216) }, { argument := 118870069412006356162969600, coefficient := (-118870069412006356162969600) }, { argument := 70777742700959182444476497920, coefficient := (-70777742700959182444476497920) }, { argument := 193319882116176336207153725440, coefficient := (-193319882116176336207153725440) }, { argument := 193178437342183273283222241280, coefficient := (-193178437342183273283222241280) }, { argument := 192848399536199459794048778240, coefficient := (-192848399536199459794048778240) }, { argument := 193178437342183273283222241280, coefficient := (-193178437342183273283222241280) }, { argument := 71026321687505086775090479104, coefficient := (-71026321687505086775090479104) }, { argument := 513437865517136816531029622784, coefficient := (-513437865517136816531029622784) }, { argument := 2641347619703167865495620681728, coefficient := (-2641347619703167865495620681728) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-470205975068066251290359923474432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    23497117665, 2297832747, 23497106913, 46920348237, 7915034527863, 55667044923,
    2297832747, 5425, 16625, 49175, 109725, 5425,
    54775, 111475, 5425, 16625, 5425, 31300222010589,
    1909243187944227, 3964599375, 10224493125, 8555188125, 239336604375, 477204017768151,
    8555188125, 7720535625, 3964599375, 3964599375, 7720535625, 239336604375,
    7720535625, 7824999200553, 10224493125, 651, 1995, 5901,
    13167, 651, 6573, 13377, 651, 1995,
    651, 19989425, 3964599375, 3964599375, 19989425, 3150903045,
    1628824317723, 17143, 63084046153521, 5425, 651, 17143,
    34069, 5425, 525791, 33635, 6515305802691, 17143,
    651, 33635, 651, 17143
  ]
def negativeCoefficients : Array ℕ := #[
    433445316036094767355542896640, 21193766304048994734965784576, 433445117696702486830443921408, 432763827888634079107923050496, 71292293100616833079072260096, 513437865517136816531029622784,
    21193766304048994734965784576, 102475352678271301137203200, 2512298968886651253686272000, 1857778974360918427068006400, 2072646649331487284291174400, 102475352678271301137203200,
    2069340992793478532641587200, 2105703214711574800787046400, 102475352678271301137203200, 2512298968886651253686272000, 102475352678271301137203200, 35240917045875604376084545536,
    2149616727446319644540978331648, 18283487506353460567080960000, 23576075995034725468078080000, 315630731688628161368555520000, 551872636047037349222154240000, 2149135836600348395846705872896,
    315630731688628161368555520000, 17802343098291527394263040000, 18283487506353460567080960000, 18283487506353460567080960000, 17802343098291527394263040000, 551872636047037349222154240000,
    17802343098291527394263040000, 35240663483784919897539084288, 23576075995034725468078080000, 6148521160696278068232192, 150737938133199075221176320, 111466738461655105624080384,
    124358798959889237057470464, 6148521160696278068232192, 124160459567608711958495232, 126342192882694488047222784, 6148521160696278068232192, 150737938133199075221176320,
    6148521160696278068232192, 92184951788902888452915200, 18283487506353460567080960000, 18283487506353460567080960000, 92184951788902888452915200, 56761623117370244758241280,
    7335572590349305183740100608, 161911057231668655796781056, 71026321687505086775090479104, 102475352678271301137203200, 6148521160696278068232192, 161911057231668655796781056,
    160886303704885942785409024, 102475352678271301137203200, 2482977795394513626554433536, 158836796651320516762664960, 7335582196301004483732701184, 161911057231668655796781056,
    6148521160696278068232192, 158836796651320516762664960, 6148521160696278068232192, 161911057231668655796781056
  ]
def negativeScales : Array ℕ := #[
    34, 31, 34, 35, 42, 35,
    31, 12, 14, 15, 16, 12,
    15, 16, 12, 14, 12, 44,
    50, 31, 33, 32, 37, 48,
    32, 32, 31, 31, 32, 37,
    32, 42, 33, 9, 10, 12,
    13, 9, 12, 13, 9, 10,
    9, 24, 31, 31, 24, 31,
    40, 14, 45, 12, 9, 14,
    15, 12, 19, 15, 42, 14,
    9, 15, 9, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34451764744581121, 31097626645941103, 34451764084420975, 35449494669783326, 42847732784171430, 35696104448919241,
    31097626645941103, 12405407422219213, 14021066720163277, 15585637432057036, 16743532744829480, 12405407422219213,
    15741229958950381, 16766360674408847, 12405407422219213, 14021066720163277, 12405407422219213, 44831238124884345,
    50761922299887652, 31884527945435175, 33251310272805963, 32994152454870937, 37800250105355915, 48761599518412991,
    32994152454870937, 32846053795925841, 31884527945435175, 31884527945435175, 32846053795925841, 37800250105355915,
    32846053795925841, 42831227744504771, 33251310272805963, 9346513733165637, 10962173043893966, 12526743743000334,
    13684639055631019, 9346513733165637, 12682336269758884, 13707466985121264, 9346513733165637, 10962173043893966,
    9346513733165637, 24252733637465689, 31884527945435175, 31884527945435175, 24252733637465689, 31553118216515278,
    40566968144221795, 14065331980621583, 45842340431279004, 12405407422219213, 9346513733165637, 14065331980621583,
    15056171981336107, 12405407422219213, 19004129921895826, 15037675637718717, 42566970033433529, 14065331980621583,
    9346513733165637, 15037675637718717, 9346513733165637, 14065331980621583
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
noncomputable def negativeCeiling : ℝ := 2153749603 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 433445316036094767355542896640, coefficient := (-433445316036094767355542896640) }, { argument := 21193766304048994734965784576, coefficient := (-21193766304048994734965784576) }, { argument := 433445117696702486830443921408, coefficient := (-433445117696702486830443921408) }, { argument := 432763827888634079107923050496, coefficient := (-432763827888634079107923050496) }, { argument := 71292293100616833079072260096, coefficient := (-71292293100616833079072260096) }, { argument := 513437865517136816531029622784, coefficient := (-513437865517136816531029622784) }, { argument := 21193766304048994734965784576, coefficient := (-21193766304048994734965784576) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 1857778974360918427068006400, coefficient := (-1857778974360918427068006400) }, { argument := 2072646649331487284291174400, coefficient := (-2072646649331487284291174400) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2069340992793478532641587200, coefficient := (-2069340992793478532641587200) }, { argument := 2105703214711574800787046400, coefficient := (-2105703214711574800787046400) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2512298968886651253686272000, coefficient := (-2512298968886651253686272000) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 35240917045875604376084545536, coefficient := (-35240917045875604376084545536) }, { argument := 2149616727446319644540978331648, coefficient := (-2149616727446319644540978331648) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 2149135836600348395846705872896, coefficient := (-2149135836600348395846705872896) }, { argument := 315630731688628161368555520000, coefficient := (-315630731688628161368555520000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 35240663483784919897539084288, coefficient := (-35240663483784919897539084288) }, { argument := 23576075995034725468078080000, coefficient := (-23576075995034725468078080000) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 56761623117370244758241280, coefficient := (-56761623117370244758241280) }, { argument := 7335572590349305183740100608, coefficient := (-7335572590349305183740100608) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 71026321687505086775090479104, coefficient := (-71026321687505086775090479104) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 7335582196301004483732701184, coefficient := (-7335582196301004483732701184) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
