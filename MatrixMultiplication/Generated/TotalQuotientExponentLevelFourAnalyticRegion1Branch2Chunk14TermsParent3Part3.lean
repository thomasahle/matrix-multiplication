import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 14, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1559232986347364888138613902016512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    30782823253, 320844218695, 30782823253, 416843791, 608552217, 22864870119,
    45726281601, 1220563071, 416843791, 30782823253, 320844218695, 30782823253,
    416843791, 608552217, 22864870119, 45726281601, 1220563071, 40186993959,
    73084379865, 40186993959, 608552217, 22864870119, 45726281601, 1220563071,
    20187245799, 36712682265, 20187245799, 1, 1, 18471359893,
    2023908244761, 418506179, 78710128373547, 13796907, 32192783, 418506179,
    418506179, 13796907, 5164642187, 206953605, 2023908244761, 418506179,
    32192783, 206953605, 32192783, 418506179, 418506179, 78592251321,
    145046231313, 14107785, 5304680569455, 222011985, 6682635, 42435397528329,
    6682635, 6682635, 572479065, 6682635, 222011985, 572479065,
    1162416877815, 6682635, 6682635, 14107785
  ]
def negativeCoefficients : Array ℕ := #[
    283921431207163165726604263424, 2959265594897981289297147330560, 283921431207163165726604263424, 1922352682822968232130904064, 5612903501243779524996366336, 210891203681900930114783281152,
    210875253534005214469165154304, 5628853649139495170614493184, 1922352682822968232130904064, 283921431207163165726604263424, 2959265594897981289297147330560, 283921431207163165726604263424,
    1922352682822968232130904064, 179612912039800944799883722752, 6748518517820829763673064996864, 6748008113088166863013284937728, 180123316772463845459663781888, 92664899081673100189098835968,
    337042212788856607495642152960, 92664899081673100189098835968, 5612903501243779524996366336, 210891203681900930114783281152, 210875253534005214469165154304, 5628853649139495170614493184,
    93097239201805323051567415296, 338614727000935254186912645120, 93097239201805323051567415296, 9903520314283042199192993792, 9903520314283042199192993792, 166375219062282249731833856,
    18229744833875428426395942912, 1930019094319769700653858816, 177239452406695086794427334656, 1018032049751087314630606848, 74231503627683450025148416, 1930019094319769700653858816,
    1930019094319769700653858816, 1018032049751087314630606848, 23817708163968146965211906048, 1908810093283288714932387840, 18229744833875428426395942912, 1930019094319769700653858816,
    74231503627683450025148416, 1908810093283288714932387840, 74231503627683450025148416, 1930019094319769700653858816, 1930019094319769700653858816, 176974016881731986006212608,
    10451682452683545100280659968, 260242699341918506644930560, 382242518974672776408732794880, 2047699134295621933864058880, 246545715166028058926776320, 382224080991802702751877562368,
    246545715166028058926776320, 246545715166028058926776320, 10560374799611535190696919040, 246545715166028058926776320, 2047699134295621933864058880, 10560374799611535190696919040,
    10470120435553618757135892480, 246545715166028058926776320, 246545715166028058926776320, 260242699341918506644930560
  ]
def negativeScales : Array ℕ := #[
    34, 38, 34, 28, 29, 34,
    35, 30, 28, 34, 38, 34,
    28, 29, 34, 35, 30, 35,
    36, 35, 29, 34, 35, 30,
    34, 35, 34, 0, 0, 34,
    40, 28, 46, 23, 24, 28,
    28, 23, 32, 27, 40, 28,
    24, 27, 24, 28, 28, 36,
    37, 23, 42, 27, 22, 45,
    22, 22, 29, 22, 27, 29,
    40, 22, 22, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34841406505150601, 38223082031238806, 34841406505150601, 28634931605203684, 29180805818216808, 34412413672995253,
    35412304554790674, 30184899700410475, 28634931605203684, 34841406505150601, 38223082031238806, 34841406505150601,
    28634931605203684, 29180805818216808, 34412413672995253, 35412304554790674, 30184899700410475, 35226009614783877,
    36088844044527201, 35226009614783877, 29180805818216808, 34412413672995253, 35412304554790674, 30184899700410475,
    34232725042149855, 35095559471893179, 34232725042149855, 0, 0, 34104571032771986,
    40880281027668647, 28640673682600610, 46161614526372748, 23717841543215820, 24940233973273646, 28640673682600610,
    28640673682600610, 23717841543215820, 32266021254785741, 27624732138725865, 40880281027668647, 28640673682600610,
    24940233973273646, 27624732138725865, 24940233973273646, 28640673682600610, 28640673682600610, 36193668028128045,
    37077721854728267, 23749988159078591, 42270403018018725, 27726062319740353, 22671985646889411, 45270333426001344,
    22671985646889411, 22671985646889411, 29092647695325218, 22671985646889411, 27726062319740353, 29092647695325218,
    40080264694222474, 22671985646889411, 22671985646889411, 23749988159078591
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
noncomputable def negativeCeiling : ℝ := 2590630483 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 5612903501243779524996366336, coefficient := (-5612903501243779524996366336) }, { argument := 210891203681900930114783281152, coefficient := (-210891203681900930114783281152) }, { argument := 210875253534005214469165154304, coefficient := (-210875253534005214469165154304) }, { argument := 5628853649139495170614493184, coefficient := (-5628853649139495170614493184) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 179612912039800944799883722752, coefficient := (-179612912039800944799883722752) }, { argument := 6748518517820829763673064996864, coefficient := (-6748518517820829763673064996864) }, { argument := 6748008113088166863013284937728, coefficient := (-6748008113088166863013284937728) }, { argument := 180123316772463845459663781888, coefficient := (-180123316772463845459663781888) }, { argument := 92664899081673100189098835968, coefficient := (-92664899081673100189098835968) }, { argument := 337042212788856607495642152960, coefficient := (-337042212788856607495642152960) }, { argument := 92664899081673100189098835968, coefficient := (-92664899081673100189098835968) }, { argument := 5612903501243779524996366336, coefficient := (-5612903501243779524996366336) }, { argument := 210891203681900930114783281152, coefficient := (-210891203681900930114783281152) }, { argument := 210875253534005214469165154304, coefficient := (-210875253534005214469165154304) }, { argument := 5628853649139495170614493184, coefficient := (-5628853649139495170614493184) }, { argument := 93097239201805323051567415296, coefficient := (-93097239201805323051567415296) }, { argument := 338614727000935254186912645120, coefficient := (-338614727000935254186912645120) }, { argument := 93097239201805323051567415296, coefficient := (-93097239201805323051567415296) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 166375219062282249731833856, coefficient := (-166375219062282249731833856) }, { argument := 18229744833875428426395942912, coefficient := (-18229744833875428426395942912) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 177239452406695086794427334656, coefficient := (-177239452406695086794427334656) }, { argument := 1018032049751087314630606848, coefficient := (-1018032049751087314630606848) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1018032049751087314630606848, coefficient := (-1018032049751087314630606848) }, { argument := 23817708163968146965211906048, coefficient := (-23817708163968146965211906048) }, { argument := 1908810093283288714932387840, coefficient := (-1908810093283288714932387840) }, { argument := 18229744833875428426395942912, coefficient := (-18229744833875428426395942912) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1908810093283288714932387840, coefficient := (-1908810093283288714932387840) }, { argument := 74231503627683450025148416, coefficient := (-74231503627683450025148416) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 1930019094319769700653858816, coefficient := (-1930019094319769700653858816) }, { argument := 176974016881731986006212608, coefficient := (-176974016881731986006212608) }, { argument := 10451682452683545100280659968, coefficient := (-10451682452683545100280659968) }, { argument := 260242699341918506644930560, coefficient := (-260242699341918506644930560) }, { argument := 382242518974672776408732794880, coefficient := (-382242518974672776408732794880) }, { argument := 2047699134295621933864058880, coefficient := (-2047699134295621933864058880) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 382224080991802702751877562368, coefficient := (-382224080991802702751877562368) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 10560374799611535190696919040, coefficient := (-10560374799611535190696919040) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 2047699134295621933864058880, coefficient := (-2047699134295621933864058880) }, { argument := 10560374799611535190696919040, coefficient := (-10560374799611535190696919040) }, { argument := 10470120435553618757135892480, coefficient := (-10470120435553618757135892480) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 260242699341918506644930560, coefficient := (-260242699341918506644930560) }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 63481642454053675476211220403453952
def positiveArguments : Array ℕ := #[
    6915, 1, 1, 1, 1, 2635,
    31535, 47175, 13685, 2635, 54655, 27455,
    2635, 31535, 2635, 25875, 20125, 2875,
    27025, 319125, 22425, 20125, 319125, 2875,
    22425, 22425, 22425, 22425, 22425, 25875,
    27025, 5025, 21105, 91455, 3015, 3015,
    7035, 91455, 91455, 3015, 1128615, 45225,
    21105, 91455
  ]
def positiveCoefficients : Array ℕ := #[
    547862743786137894459356416573440, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 50968312554952766005612380160,
    1219951223089514592779496325120, 912497208645122101068221644800, 1058825589851276816374657187840, 50968312554952766005612380160, 1057181450736600920697056788480, 1062113868080628607729857986560,
    50968312554952766005612380160, 1219951223089514592779496325120, 50968312554952766005612380160, 1000990578640912956656713728000, 778548227831821188510777344000, 889769403236367072583745536000,
    1045479048802731310285901004800, 12345550469904593132099469312000, 27760805380974652664612860723200, 778548227831821188510777344000, 12345550469904593132099469312000, 889769403236367072583745536000,
    867525168155457895769151897600, 867525168155457895769151897600, 867525168155457895769151897600, 27760805380974652664612860723200, 867525168155457895769151897600, 1000990578640912956656713728000,
    1045479048802731310285901004800, 194395271794032371292753100800, 3265840566139743837718252093440, 7075987893302778315056212869120, 233274326152838845551303720960, 3732389218445421528820859535360,
    272153380511645319809854341120, 7075987893302778315056212869120, 7075987893302778315056212869120, 3732389218445421528820859535360, 87322356089879341184704692879360, 6998229784585165366539111628800,
    3265840566139743837718252093440, 7075987893302778315056212869120
  ]
def positiveScales : Array ℕ := #[
    12, 0, 0, 0, 0, 11,
    14, 15, 13, 11, 15, 14,
    11, 14, 11, 14, 14, 11,
    14, 18, 14, 14, 18, 11,
    14, 14, 14, 14, 14, 14,
    14, 12, 14, 16, 11, 11,
    12, 16, 16, 11, 20, 15,
    14, 16
  ]
def negativeArguments : Array ℕ := #[
    54738645397119, 196772731145061, 13684658119047, 733383441, 27555099887, 55106031673,
    1470934983, 23187208023, 42168436905, 23187208023, 1, 1,
    1937475603, 3523508205, 1937475603, 1, 1, 1,
    85, 575
  ]
def negativeCoefficients : Array ℕ := #[
    15407558938326927777479000064, 55386599916348219518160470016, 15407555301408175472485859328, 6764268322011734299354595328, 254150937770495992702431133696, 254131715797390899488481083392,
    6783490295116827513304645632, 106932123046036454650561953792, 388935181787451948307568394240, 106932123046036454650561953792, 9903520314283042199192993792, 9903520314283042199192993792,
    4467514574699636245508653056, 16249313524812682476461752320, 4467514574699636245508653056, 9903520314283042199192993792, 9903520314283042199192993792, 158456325028528675187087900672,
    6734393813712468695451235778560, 91112386891403988232575542886400
  ]
def negativeScales : Array ℕ := #[
    45, 47, 43, 29, 34, 35,
    30, 34, 35, 34, 0, 0,
    30, 31, 30, 0, 0, 0,
    6, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12755513536022131, 0, 0, 0, 0, 11363587246524576,
    14944666312170518, 15525734897375130, 13740307814241047, 11363587246524576, 15738065863454924, 14744781290819185,
    11363587246524576, 14944666312170518, 11363587246524576, 14659271242159738, 14296701162776703, 11489346240719087,
    14722006997501899, 18283762107069205, 14452820364693982, 14296701162776703, 18283762107069205, 11489346240719087,
    14452820364693982, 14452820364693982, 14452820364693982, 14452820364693982, 14452820364693982, 14659271242159738,
    14722006997501899, 12294907880953653, 14365297208845050, 16480774426264977, 11557942286787341, 11557942286787341,
    12780334708097221, 16480774426264977, 16480774426264977, 11557942286787341, 20106121998466892, 15464832882395960,
    14365297208845050, 16480774426264977
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    45637624966700563, 47483523633614673, 43637624626155686, 29449992451032244, 34681600305857299, 35681491187652596,
    30454086333225918, 34432610064076757, 35295444493820058, 34432610064076757, 0, 0,
    30851530999626243, 31714365427687252, 30851530999626243, 0, 0, 0,
    6409390936137712, 9167418145831738
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 212122479 / 1600000000
noncomputable def negativeCeiling : ℝ := 11105449741 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15407558938326927777479000064, coefficient := (-15407558938326927777479000064) }, { argument := 55386599916348219518160470016, coefficient := (-55386599916348219518160470016) }, { argument := 15407555301408175472485859328, coefficient := (-15407555301408175472485859328) }, { argument := 6764268322011734299354595328, coefficient := (-6764268322011734299354595328) }, { argument := 254150937770495992702431133696, coefficient := (-254150937770495992702431133696) }, { argument := 254131715797390899488481083392, coefficient := (-254131715797390899488481083392) }, { argument := 6783490295116827513304645632, coefficient := (-6783490295116827513304645632) }, { argument := 106932123046036454650561953792, coefficient := (-106932123046036454650561953792) }, { argument := 388935181787451948307568394240, coefficient := (-388935181787451948307568394240) }, { argument := 106932123046036454650561953792, coefficient := (-106932123046036454650561953792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 4467514574699636245508653056, coefficient := (-4467514574699636245508653056) }, { argument := 16249313524812682476461752320, coefficient := (-16249313524812682476461752320) }, { argument := 4467514574699636245508653056, coefficient := (-4467514574699636245508653056) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 547862743786137894459356416573440, coefficient := 547862743786137894459356416573440 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 912497208645122101068221644800, coefficient := 912497208645122101068221644800 }, { argument := 1058825589851276816374657187840, coefficient := 1058825589851276816374657187840 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1057181450736600920697056788480, coefficient := 1057181450736600920697056788480 }, { argument := 1062113868080628607729857986560, coefficient := 1062113868080628607729857986560 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 50968312554952766005612380160, coefficient := 50968312554952766005612380160 }, { argument := 6734393813712468695451235778560, coefficient := (-6734393813712468695451235778560) }, { argument := 1000990578640912956656713728000, coefficient := 1000990578640912956656713728000 }, { argument := 778548227831821188510777344000, coefficient := 778548227831821188510777344000 }, { argument := 889769403236367072583745536000, coefficient := 889769403236367072583745536000 }, { argument := 1045479048802731310285901004800, coefficient := 1045479048802731310285901004800 }, { argument := 12345550469904593132099469312000, coefficient := 12345550469904593132099469312000 }, { argument := 27760805380974652664612860723200, coefficient := 27760805380974652664612860723200 }, { argument := 778548227831821188510777344000, coefficient := 778548227831821188510777344000 }, { argument := 12345550469904593132099469312000, coefficient := 12345550469904593132099469312000 }, { argument := 889769403236367072583745536000, coefficient := 889769403236367072583745536000 }, { argument := 867525168155457895769151897600, coefficient := 867525168155457895769151897600 }, { argument := 867525168155457895769151897600, coefficient := 867525168155457895769151897600 }, { argument := 867525168155457895769151897600, coefficient := 867525168155457895769151897600 }, { argument := 27760805380974652664612860723200, coefficient := 27760805380974652664612860723200 }, { argument := 867525168155457895769151897600, coefficient := 867525168155457895769151897600 }, { argument := 1000990578640912956656713728000, coefficient := 1000990578640912956656713728000 }, { argument := 1045479048802731310285901004800, coefficient := 1045479048802731310285901004800 }, { argument := 91112386891403988232575542886400, coefficient := (-91112386891403988232575542886400) }, { argument := 194395271794032371292753100800, coefficient := 194395271794032371292753100800 }, { argument := 3265840566139743837718252093440, coefficient := 3265840566139743837718252093440 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }, { argument := 233274326152838845551303720960, coefficient := 233274326152838845551303720960 }, { argument := 3732389218445421528820859535360, coefficient := 3732389218445421528820859535360 }, { argument := 272153380511645319809854341120, coefficient := 272153380511645319809854341120 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }, { argument := 3732389218445421528820859535360, coefficient := 3732389218445421528820859535360 }, { argument := 87322356089879341184704692879360, coefficient := 87322356089879341184704692879360 }, { argument := 6998229784585165366539111628800, coefficient := 6998229784585165366539111628800 }, { argument := 3265840566139743837718252093440, coefficient := 3265840566139743837718252093440 }, { argument := 7075987893302778315056212869120, coefficient := 7075987893302778315056212869120 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
