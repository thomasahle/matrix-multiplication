import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7

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
def constantNumerator : ℤ := 184890230537231502342917233573888
def positiveArguments : Array ℕ := #[
    49, 8388589
  ]
def positiveCoefficients : Array ℕ := #[
    3882179963198952542083653566464, 79227983064337988547025829888
  ]
def positiveScales : Array ℕ := #[
    5, 22
  ]
def negativeArguments : Array ℕ := #[
    335702943191, 69025445866377, 34520746618567, 1327418711949, 68858712575, 43439831239245,
    60074504496665, 43440165906545, 550786285125, 1351788742305, 47317946087675, 47319721084855,
    1350021937325, 68858712575, 472339284097, 137728973697, 335704463913, 69025758549111,
    34520902996281, 1327424725107, 472339284097, 149205413621621, 412709362580773, 149206556218745,
    1889070989627, 47317946087675, 207903823497455, 1663295921846145, 11813234893315, 43439831239245,
    149205413621621, 21722179724063, 335702943191, 335704463913, 137728973697, 21722179724063,
    120161643001513, 21722347061515, 4303378689, 47319721084855, 1663295921846145, 51980039245495,
    5906839303485, 60074504496665, 412709362580773, 120161643001513, 69025445866377, 69025758549111,
    1350021937325, 11813234893315, 5906839303485, 1348255274335, 43440165906545, 149206556218745,
    21722347061515, 34520746618567, 34520902996281, 550786285125, 1889070989627, 4303378689,
    1327418711949, 1327424725107
  ]
def negativeCoefficients : Array ℕ := #[
    377967912465541596849373184, 19428935767681112539568013312, 19433452700991206376712699904, 373635151031133760382828544, 310112072293982087099187200, 12227225486381313342276894720,
    135275758032823840180975697920, 12227319686851786660401643520, 310065113556216220483584000, 380494704758026840131502080, 13318817773024396815682764800, 13319317390314298795758714880,
    379997393367429069091635200, 310112072293982087099187200, 1063613511925848023609901056, 310138077309965022428921856, 377969624646299730378227712, 19429023780046383013813026816,
    19433540733818018807962140672, 373636843584641767877640192, 1063613511925848023609901056, 41997590324249566478782693376, 464669432882771052042599268352, 41997911936748434041308446720,
    1063452425620071414312730624, 13318817773024396815682764800, 468157791016019854219899043840, 468176180864572766203014021120, 13300520065893393767134658560, 12227225486381313342276894720,
    41997590324249566478782693376, 12228500063870633802943430656, 377967912465541596849373184, 377969624646299730378227712, 310138077309965022428921856, 12228500063870633802943430656,
    135289982661460128830284890112, 12228594266481442843976007680, 310091114563432537500155904, 13319317390314298795758714880, 468176180864572766203014021120, 468194570753430080101327831040,
    13301019643056223067339489280, 135275758032823840180975697920, 464669432882771052042599268352, 135289982661460128830284890112, 19428935767681112539568013312, 19429023780046383013813026816,
    379997393367429069091635200, 13300520065893393767134658560, 13301019643056223067339489280, 379500121943463241197813760, 12227319686851786660401643520, 41997911936748434041308446720,
    12228594266481442843976007680, 19433452700991206376712699904, 19433540733818018807962140672, 310065113556216220483584000, 1063452425620071414312730624, 310091114563432537500155904,
    373635151031133760382828544, 373636843584641767877640192
  ]
def negativeScales : Array ℕ := #[
    38, 45, 44, 40, 36, 45,
    45, 45, 39, 40, 45, 45,
    40, 36, 38, 37, 38, 45,
    44, 40, 38, 47, 48, 47,
    40, 45, 47, 50, 43, 45,
    47, 44, 38, 38, 37, 44,
    46, 44, 32, 45, 50, 45,
    42, 45, 48, 46, 45, 45,
    40, 43, 42, 40, 45, 47,
    44, 44, 44, 39, 40, 32,
    40, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5614709844114682, 22999996730866427
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38288394229317291, 45972193550485420, 44972528916333742, 40271760655076062, 36002920156516479, 45304083731917920,
    45771818077739007, 45304094846624870, 39002701679797965, 40298006843342969, 45427452686050386, 45427506803606450,
    40296119989341378, 36002920156516479, 38781032572519171, 37003041131280105, 38288400764658024, 45972200085827776,
    44972535451676106, 40271767190416794, 38781032572519171, 47084293210285495, 48552119495617606, 47084304258228414,
    40780814057039270, 45427452686050386, 47562909619041198, 50562966288870792, 43425469314739277, 45304083731917920,
    47084293210285495, 44304234111968674, 38288394229317291, 38288400764658024, 37003041131280105, 44304234111968674,
    46771969773229463, 44304245225769653, 32002822654231472, 45427506803606450, 50562966288870792, 45563022956598647,
    42425523502391821, 45771818077739007, 48552119495617606, 46771969773229463, 45972193550485420, 45972200085827776,
    40296119989341378, 43425469314739277, 42425523502391821, 40294230816288452, 45304094846624870, 47084304258228414,
    44304245225769653, 44972528916333742, 44972535451676106, 39002701679797965, 40780814057039270, 32002822654231472,
    40271760655076062, 40271767190416794
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 888469 / 3125000000
noncomputable def negativeCeiling : ℝ := 446834441 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 377967912465541596849373184, coefficient := (-377967912465541596849373184) }, { argument := 19428935767681112539568013312, coefficient := (-19428935767681112539568013312) }, { argument := 19433452700991206376712699904, coefficient := (-19433452700991206376712699904) }, { argument := 373635151031133760382828544, coefficient := (-373635151031133760382828544) }, { argument := 310112072293982087099187200, coefficient := (-310112072293982087099187200) }, { argument := 12227225486381313342276894720, coefficient := (-12227225486381313342276894720) }, { argument := 135275758032823840180975697920, coefficient := (-135275758032823840180975697920) }, { argument := 12227319686851786660401643520, coefficient := (-12227319686851786660401643520) }, { argument := 310065113556216220483584000, coefficient := (-310065113556216220483584000) }, { argument := 380494704758026840131502080, coefficient := (-380494704758026840131502080) }, { argument := 13318817773024396815682764800, coefficient := (-13318817773024396815682764800) }, { argument := 13319317390314298795758714880, coefficient := (-13319317390314298795758714880) }, { argument := 379997393367429069091635200, coefficient := (-379997393367429069091635200) }, { argument := 310112072293982087099187200, coefficient := (-310112072293982087099187200) }, { argument := 1063613511925848023609901056, coefficient := (-1063613511925848023609901056) }, { argument := 310138077309965022428921856, coefficient := (-310138077309965022428921856) }, { argument := 377969624646299730378227712, coefficient := (-377969624646299730378227712) }, { argument := 19429023780046383013813026816, coefficient := (-19429023780046383013813026816) }, { argument := 19433540733818018807962140672, coefficient := (-19433540733818018807962140672) }, { argument := 373636843584641767877640192, coefficient := (-373636843584641767877640192) }, { argument := 1063613511925848023609901056, coefficient := (-1063613511925848023609901056) }, { argument := 41997590324249566478782693376, coefficient := (-41997590324249566478782693376) }, { argument := 464669432882771052042599268352, coefficient := (-464669432882771052042599268352) }, { argument := 41997911936748434041308446720, coefficient := (-41997911936748434041308446720) }, { argument := 1063452425620071414312730624, coefficient := (-1063452425620071414312730624) }, { argument := 13318817773024396815682764800, coefficient := (-13318817773024396815682764800) }, { argument := 468157791016019854219899043840, coefficient := (-468157791016019854219899043840) }, { argument := 468176180864572766203014021120, coefficient := (-468176180864572766203014021120) }, { argument := 13300520065893393767134658560, coefficient := (-13300520065893393767134658560) }, { argument := 12227225486381313342276894720, coefficient := (-12227225486381313342276894720) }, { argument := 41997590324249566478782693376, coefficient := (-41997590324249566478782693376) }, { argument := 12228500063870633802943430656, coefficient := (-12228500063870633802943430656) }, { argument := 377967912465541596849373184, coefficient := (-377967912465541596849373184) }, { argument := 377969624646299730378227712, coefficient := (-377969624646299730378227712) }, { argument := 310138077309965022428921856, coefficient := (-310138077309965022428921856) }, { argument := 12228500063870633802943430656, coefficient := (-12228500063870633802943430656) }, { argument := 135289982661460128830284890112, coefficient := (-135289982661460128830284890112) }, { argument := 12228594266481442843976007680, coefficient := (-12228594266481442843976007680) }, { argument := 310091114563432537500155904, coefficient := (-310091114563432537500155904) }, { argument := 13319317390314298795758714880, coefficient := (-13319317390314298795758714880) }, { argument := 468176180864572766203014021120, coefficient := (-468176180864572766203014021120) }, { argument := 468194570753430080101327831040, coefficient := (-468194570753430080101327831040) }, { argument := 13301019643056223067339489280, coefficient := (-13301019643056223067339489280) }, { argument := 135275758032823840180975697920, coefficient := (-135275758032823840180975697920) }, { argument := 464669432882771052042599268352, coefficient := (-464669432882771052042599268352) }, { argument := 135289982661460128830284890112, coefficient := (-135289982661460128830284890112) }, { argument := 19428935767681112539568013312, coefficient := (-19428935767681112539568013312) }, { argument := 19429023780046383013813026816, coefficient := (-19429023780046383013813026816) }, { argument := 379997393367429069091635200, coefficient := (-379997393367429069091635200) }, { argument := 13300520065893393767134658560, coefficient := (-13300520065893393767134658560) }, { argument := 13301019643056223067339489280, coefficient := (-13301019643056223067339489280) }, { argument := 379500121943463241197813760, coefficient := (-379500121943463241197813760) }, { argument := 12227319686851786660401643520, coefficient := (-12227319686851786660401643520) }, { argument := 41997911936748434041308446720, coefficient := (-41997911936748434041308446720) }, { argument := 12228594266481442843976007680, coefficient := (-12228594266481442843976007680) }, { argument := 19433452700991206376712699904, coefficient := (-19433452700991206376712699904) }, { argument := 19433540733818018807962140672, coefficient := (-19433540733818018807962140672) }, { argument := 310065113556216220483584000, coefficient := (-310065113556216220483584000) }, { argument := 1063452425620071414312730624, coefficient := (-1063452425620071414312730624) }, { argument := 310091114563432537500155904, coefficient := (-310091114563432537500155904) }, { argument := 373635151031133760382828544, coefficient := (-373635151031133760382828544) }, { argument := 373636843584641767877640192, coefficient := (-373636843584641767877640192) }, { argument := 3882179963198952542083653566464, coefficient := 3882179963198952542083653566464 }, { argument := 79227983064337988547025829888, coefficient := 79227983064337988547025829888 }] }

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
def constantNumerator : ℤ := (-187305274934445029414995425755136)
def positiveArguments : Array ℕ := #[
    8388627, 33955535, 116634743, 16979549, 5801885, 203913295,
    203921295, 5793925, 89143, 14072037, 19461513, 14072145,
    178259, 40019, 8228493, 4115203, 158241
  ]
def positiveCoefficients : Array ℕ := #[
    79228341964190686640062070784, 320700960783814276982474014720, 1101584002162629944001226080256, 320734612367371206074266812416, 54797254522928303041329233920, 1925906619439020822011460976640,
    1925982177302746736334880112640, 54722074448521018289527193600, 3367727323059590266276020224, 132906631749003027248006037504, 1470470347154110042107719712768, 132907651780163327091372195840,
    3367217307479440344592941056, 1511875074223682654455201792, 77715919095454991106762080256, 77733986869618450369349681152, 1494543989231551056520937472
  ]
def positiveScales : Array ℕ := #[
    23, 25, 26, 24, 22, 27,
    27, 22, 16, 23, 24, 23,
    17, 15, 22, 21, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 11, 25, 11, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1743019575313815427057966907392, 3961408125713216879677197516800, 1743019575313815427057966907392, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 3, 4, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23000003267666665, 25017143427670747, 26797422359672195, 24017294803661703, 22468090269276839, 27603380600197373,
    27603437199419761, 22466109578953475, 16443833893476159, 23746327845444537, 24214120538397664, 23746338917790813,
    17443615392214447, 15288397496991357, 22972196802137821, 21972532167897502, 17271763922750127
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3459431618637364, 4643856189792934, 3459431618637364, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 242460771 / 100000000000
noncomputable def negativeCeiling : ℝ := 366599847 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228341964190686640062070784, coefficient := 79228341964190686640062070784 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 320700960783814276982474014720, coefficient := 320700960783814276982474014720 }, { argument := 1101584002162629944001226080256, coefficient := 1101584002162629944001226080256 }, { argument := 320734612367371206074266812416, coefficient := 320734612367371206074266812416 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 54797254522928303041329233920, coefficient := 54797254522928303041329233920 }, { argument := 1925906619439020822011460976640, coefficient := 1925906619439020822011460976640 }, { argument := 1925982177302746736334880112640, coefficient := 1925982177302746736334880112640 }, { argument := 54722074448521018289527193600, coefficient := 54722074448521018289527193600 }, { argument := 3961408125713216879677197516800, coefficient := (-3961408125713216879677197516800) }, { argument := 3367727323059590266276020224, coefficient := 3367727323059590266276020224 }, { argument := 132906631749003027248006037504, coefficient := 132906631749003027248006037504 }, { argument := 1470470347154110042107719712768, coefficient := 1470470347154110042107719712768 }, { argument := 132907651780163327091372195840, coefficient := 132907651780163327091372195840 }, { argument := 3367217307479440344592941056, coefficient := 3367217307479440344592941056 }, { argument := 1743019575313815427057966907392, coefficient := (-1743019575313815427057966907392) }, { argument := 1511875074223682654455201792, coefficient := 1511875074223682654455201792 }, { argument := 77715919095454991106762080256, coefficient := 77715919095454991106762080256 }, { argument := 77733986869618450369349681152, coefficient := 77733986869618450369349681152 }, { argument := 1494543989231551056520937472, coefficient := 1494543989231551056520937472 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7
