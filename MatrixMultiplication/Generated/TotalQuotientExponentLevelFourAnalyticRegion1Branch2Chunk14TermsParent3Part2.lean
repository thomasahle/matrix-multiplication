import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4418391429247258747044646396887040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5144127223, 8660166165, 325384690155, 650720161245, 17369551395, 206131545,
    15222275235, 158659229025, 15222275235, 206131545, 608552217, 22864870119,
    45726281601, 1220563071, 23187208023, 42168436905, 23187208023, 4643333193675,
    149288100708405, 4907115, 46126881, 544689765, 38275497, 74644035075135,
    544689765, 4907115, 38275497, 38275497, 38275497, 38275497,
    38275497, 2321681875905, 46126881, 463468596469, 42648146058361, 30905586257,
    1564014712553803, 1018865481, 2377352789, 30905586257, 30905586257, 1018865481,
    381395311721, 15282982215, 42648146058361, 30905586257, 2377352789, 15282982215,
    2377352789, 30905586257, 30905586257, 2027659672857, 4707742383855, 1181268855,
    164722324819345, 18589441455, 559548405, 1317776692262135, 559548405, 559548405,
    47934646695, 559548405, 18589441455, 47934646695
  ]
def negativeCoefficients : Array ℕ := #[
    23723099591320805765747310592, 79875934440776862471102136320, 3001144052396282467018069770240, 3000917069522381898215042580480, 80102917314677431274129326080, 1901227928066671877931663360,
    280801415479611922147191029760, 2926746192756245231173002854400, 280801415479611922147191029760, 1901227928066671877931663360, 179612912039800944799883722752, 6748518517820829763673064996864,
    6748008113088166863013284937728, 180123316772463845459663781888, 106932123046036454650561953792, 388935181787451948307568394240, 106932123046036454650561953792, 10455856820395892567074406400,
    336166917360610918962498109440, 5793298850896719768201461760, 6807126149803645727636717568, 80382021556191986783795281920, 180750924147977656767885606912, 336166848549808219393842216960,
    80382021556191986783795281920, 5793298850896719768201461760, 5648466379624301773996425216, 5648466379624301773996425216, 5648466379624301773996425216, 180750924147977656767885606912,
    5648466379624301773996425216, 10455925631198592135730298880, 6807126149803645727636717568, 16698215986845721425443028992, 1536561397571816698827084136448, 285053720065417056716540870656,
    14087392153318561206347629592576, 150358006188351854092241338368, 10963604617900656027559264256, 285053720065417056716540870656, 285053720065417056716540870656, 150358006188351854092241338368,
    3517750853114981919699729645568, 281921261603159726422952509440, 1536561397571816698827084136448, 285053720065417056716540870656, 10963604617900656027559264256, 281921261603159726422952509440,
    10963604617900656027559264256, 285053720065417056716540870656, 285053720065417056716540870656, 18263534694225934044987654144, 339228589530970696709339873280, 21790564250428917639995719680,
    11869494410816063149449328721920, 171457334496795957219966320640, 20643692447774764079995944960, 11869477240458551931199993937920, 20643692447774764079995944960, 20643692447774764079995944960,
    884238159846352394759826309120, 20643692447774764079995944960, 171457334496795957219966320640, 884238159846352394759826309120
  ]
def negativeScales : Array ℕ := #[
    32, 33, 38, 39, 34, 27,
    33, 37, 33, 27, 29, 34,
    35, 30, 34, 35, 34, 42,
    47, 22, 25, 29, 25, 46,
    29, 22, 25, 25, 25, 25,
    25, 41, 25, 38, 45, 34,
    50, 29, 31, 34, 34, 29,
    38, 33, 45, 34, 31, 33,
    31, 34, 34, 40, 42, 30,
    47, 34, 29, 50, 29, 29,
    35, 29, 34, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32260279177391137, 33011747560592028, 38243355415370463, 39243246297165883, 34015841442785695, 27618990061329693,
    33825464960889115, 37207140487369785, 33825464960889115, 27618990061329693, 29180805818216808, 34412413672995253,
    35412304554790674, 30184899700410475, 34432610064076757, 35295444493820058, 34432610064076757, 42078297947361534,
    47085092505729941, 22226443651202214, 25459104407992554, 29020859517552320, 25189917775177100, 46085092210421245,
    29020859517552320, 22226443651202214, 25189917775177100, 25189917775177100, 25189917775177100, 25189917775177100,
    25189917775177100, 41078307441817977, 25459104407992554, 38753680632578631, 45277548261584724, 34847148582716669,
    50474175507329582, 29924316448310161, 31146708862935373, 34847148582716669, 34847148582716669, 29924316448310161,
    38472496153278476, 33831207038412152, 45277548261584724, 34847148582716669, 31146708862935373, 33831207038412152,
    31146708862935373, 34847148582716669, 34847148582716669, 40882952669204824, 42098172514312800, 30137690211297030,
    47227029425220736, 34113764372051550, 29059687699295757, 50227027338223035, 29059687699295757, 29059687699295757,
    35480349747768618, 29059687699295757, 34113764372051550, 35480349747768618
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
noncomputable def negativeCeiling : ℝ := 7802175853 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23723099591320805765747310592, coefficient := (-23723099591320805765747310592) }, { argument := 79875934440776862471102136320, coefficient := (-79875934440776862471102136320) }, { argument := 3001144052396282467018069770240, coefficient := (-3001144052396282467018069770240) }, { argument := 3000917069522381898215042580480, coefficient := (-3000917069522381898215042580480) }, { argument := 80102917314677431274129326080, coefficient := (-80102917314677431274129326080) }, { argument := 1901227928066671877931663360, coefficient := (-1901227928066671877931663360) }, { argument := 280801415479611922147191029760, coefficient := (-280801415479611922147191029760) }, { argument := 2926746192756245231173002854400, coefficient := (-2926746192756245231173002854400) }, { argument := 280801415479611922147191029760, coefficient := (-280801415479611922147191029760) }, { argument := 1901227928066671877931663360, coefficient := (-1901227928066671877931663360) }, { argument := 179612912039800944799883722752, coefficient := (-179612912039800944799883722752) }, { argument := 6748518517820829763673064996864, coefficient := (-6748518517820829763673064996864) }, { argument := 6748008113088166863013284937728, coefficient := (-6748008113088166863013284937728) }, { argument := 180123316772463845459663781888, coefficient := (-180123316772463845459663781888) }, { argument := 106932123046036454650561953792, coefficient := (-106932123046036454650561953792) }, { argument := 388935181787451948307568394240, coefficient := (-388935181787451948307568394240) }, { argument := 106932123046036454650561953792, coefficient := (-106932123046036454650561953792) }, { argument := 10455856820395892567074406400, coefficient := (-10455856820395892567074406400) }, { argument := 336166917360610918962498109440, coefficient := (-336166917360610918962498109440) }, { argument := 5793298850896719768201461760, coefficient := (-5793298850896719768201461760) }, { argument := 6807126149803645727636717568, coefficient := (-6807126149803645727636717568) }, { argument := 80382021556191986783795281920, coefficient := (-80382021556191986783795281920) }, { argument := 180750924147977656767885606912, coefficient := (-180750924147977656767885606912) }, { argument := 336166848549808219393842216960, coefficient := (-336166848549808219393842216960) }, { argument := 80382021556191986783795281920, coefficient := (-80382021556191986783795281920) }, { argument := 5793298850896719768201461760, coefficient := (-5793298850896719768201461760) }, { argument := 5648466379624301773996425216, coefficient := (-5648466379624301773996425216) }, { argument := 5648466379624301773996425216, coefficient := (-5648466379624301773996425216) }, { argument := 5648466379624301773996425216, coefficient := (-5648466379624301773996425216) }, { argument := 180750924147977656767885606912, coefficient := (-180750924147977656767885606912) }, { argument := 5648466379624301773996425216, coefficient := (-5648466379624301773996425216) }, { argument := 10455925631198592135730298880, coefficient := (-10455925631198592135730298880) }, { argument := 6807126149803645727636717568, coefficient := (-6807126149803645727636717568) }, { argument := 16698215986845721425443028992, coefficient := (-16698215986845721425443028992) }, { argument := 1536561397571816698827084136448, coefficient := (-1536561397571816698827084136448) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 14087392153318561206347629592576, coefficient := (-14087392153318561206347629592576) }, { argument := 150358006188351854092241338368, coefficient := (-150358006188351854092241338368) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 150358006188351854092241338368, coefficient := (-150358006188351854092241338368) }, { argument := 3517750853114981919699729645568, coefficient := (-3517750853114981919699729645568) }, { argument := 281921261603159726422952509440, coefficient := (-281921261603159726422952509440) }, { argument := 1536561397571816698827084136448, coefficient := (-1536561397571816698827084136448) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 281921261603159726422952509440, coefficient := (-281921261603159726422952509440) }, { argument := 10963604617900656027559264256, coefficient := (-10963604617900656027559264256) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 285053720065417056716540870656, coefficient := (-285053720065417056716540870656) }, { argument := 18263534694225934044987654144, coefficient := (-18263534694225934044987654144) }, { argument := 339228589530970696709339873280, coefficient := (-339228589530970696709339873280) }, { argument := 21790564250428917639995719680, coefficient := (-21790564250428917639995719680) }, { argument := 11869494410816063149449328721920, coefficient := (-11869494410816063149449328721920) }, { argument := 171457334496795957219966320640, coefficient := (-171457334496795957219966320640) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 11869477240458551931199993937920, coefficient := (-11869477240458551931199993937920) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 884238159846352394759826309120, coefficient := (-884238159846352394759826309120) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 171457334496795957219966320640, coefficient := (-171457334496795957219966320640) }, { argument := 884238159846352394759826309120, coefficient := (-884238159846352394759826309120) }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1049607863676407555877365990031360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37663845363465, 559548405, 559548405, 1181268855, 416843791, 30782823253,
    320844218695, 30782823253, 416843791, 8660166165, 325384690155, 650720161245,
    17369551395, 330311762813313, 1190162183197851, 82577925059193, 78019515, 2931393605,
    5862343795, 156482445, 10062373293, 18299510355, 10062373293, 1,
    1, 13365675, 1119096405, 559548405, 6682635, 32064907,
    2367909481, 24680324515, 2367909481, 32064907, 13365675, 1119096405,
    559548405, 6682635, 206131545, 15222275235, 158659229025, 15222275235,
    206131545, 608552217, 22864870119, 45726281601, 1220563071, 32064907,
    2367909481, 24680324515, 2367909481, 32064907, 608552217, 22864870119,
    45726281601, 1220563071, 1937475603, 3523508205, 1937475603, 28216425,
    2362536855, 1181268855, 14107785, 416843791
  ]
def negativeCoefficients : Array ℕ := #[
    339245759888481914958674657280, 20643692447774764079995944960, 20643692447774764079995944960, 21790564250428917639995719680, 1922352682822968232130904064, 283921431207163165726604263424,
    2959265594897981289297147330560, 283921431207163165726604263424, 1922352682822968232130904064, 79875934440776862471102136320, 3001144052396282467018069770240, 3000917069522381898215042580480,
    80102917314677431274129326080, 185948991490266010538691526656, 670001745595037219878456000512, 185948956262805169321870884864, 5756824103839773871791144960, 216298670442975312938239262720,
    216282311316928425096579645440, 5773183229886661713450762240, 92809012455050507809921695744, 337566384192882823059398983680, 92809012455050507809921695744, 9903520314283042199192993792,
    9903520314283042199192993792, 246553186097377911295180800, 20643684976843414227627540480, 20643692447774764079995944960, 246545715166028058926776320, 73936641647037239697342464,
    10920055046429352527946317824, 113817907496076203434505666560, 10920055046429352527946317824, 73936641647037239697342464, 246553186097377911295180800, 20643684976843414227627540480,
    20643692447774764079995944960, 246545715166028058926776320, 1901227928066671877931663360, 280801415479611922147191029760, 2926746192756245231173002854400, 280801415479611922147191029760,
    1901227928066671877931663360, 5612903501243779524996366336, 210891203681900930114783281152, 210875253534005214469165154304, 5628853649139495170614493184, 73936641647037239697342464,
    10920055046429352527946317824, 113817907496076203434505666560, 10920055046429352527946317824, 73936641647037239697342464, 5612903501243779524996366336, 210891203681900930114783281152,
    210875253534005214469165154304, 5628853649139495170614493184, 4467514574699636245508653056, 16249313524812682476461752320, 4467514574699636245508653056, 260250585325010017478246400,
    21790556364445826129162403840, 21790564250428917639995719680, 260242699341918506644930560, 1922352682822968232130904064
  ]
def negativeScales : Array ℕ := #[
    45, 29, 29, 30, 28, 34,
    38, 34, 28, 33, 38, 39,
    34, 48, 50, 46, 26, 31,
    32, 27, 33, 34, 33, 0,
    0, 23, 30, 29, 22, 24,
    31, 34, 31, 24, 23, 30,
    29, 22, 27, 33, 37, 33,
    27, 29, 34, 35, 30, 24,
    31, 34, 31, 24, 29, 34,
    35, 30, 30, 31, 30, 24,
    31, 30, 23, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    45098245535760577, 29059687699295757, 29059687699295757, 30137690211297030, 28634931605203684, 34841406505150601,
    38223082031238806, 34841406505150601, 28634931605203684, 33011747560592028, 38243355415370463, 39243246297165883,
    34015841442785695, 48230821675128758, 50080079606047237, 46230821401814622, 26217331694241922, 31448939549020401,
    32448830430815822, 27221425576435589, 33228251565570547, 34091085995313871, 33228251565570547, 0,
    0, 23672029363375464, 30059687177185791, 29059687699295757, 22671985646889411, 24934491895051345,
    31140966785540769, 34522642313098282, 31140966785540769, 24934491895051345, 23672029363375464, 30059687177185791,
    29059687699295757, 22671985646889411, 27618990061329693, 33825464960889115, 37207140487369785, 33825464960889115,
    27618990061329693, 29180805818216808, 34412413672995253, 35412304554790674, 30184899700410475, 24934491895051345,
    31140966785540769, 34522642313098282, 31140966785540769, 24934491895051345, 29180805818216808, 34412413672995253,
    35412304554790674, 30184899700410475, 30851530999626243, 31714365427687252, 30851530999626243, 24750031875564819,
    31137689689187065, 30137690211297030, 23749988159078591, 28634931605203684
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
noncomputable def negativeCeiling : ℝ := 7739653369 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 339245759888481914958674657280, coefficient := (-339245759888481914958674657280) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 21790564250428917639995719680, coefficient := (-21790564250428917639995719680) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 2959265594897981289297147330560, coefficient := (-2959265594897981289297147330560) }, { argument := 283921431207163165726604263424, coefficient := (-283921431207163165726604263424) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }, { argument := 79875934440776862471102136320, coefficient := (-79875934440776862471102136320) }, { argument := 3001144052396282467018069770240, coefficient := (-3001144052396282467018069770240) }, { argument := 3000917069522381898215042580480, coefficient := (-3000917069522381898215042580480) }, { argument := 80102917314677431274129326080, coefficient := (-80102917314677431274129326080) }, { argument := 185948991490266010538691526656, coefficient := (-185948991490266010538691526656) }, { argument := 670001745595037219878456000512, coefficient := (-670001745595037219878456000512) }, { argument := 185948956262805169321870884864, coefficient := (-185948956262805169321870884864) }, { argument := 5756824103839773871791144960, coefficient := (-5756824103839773871791144960) }, { argument := 216298670442975312938239262720, coefficient := (-216298670442975312938239262720) }, { argument := 216282311316928425096579645440, coefficient := (-216282311316928425096579645440) }, { argument := 5773183229886661713450762240, coefficient := (-5773183229886661713450762240) }, { argument := 92809012455050507809921695744, coefficient := (-92809012455050507809921695744) }, { argument := 337566384192882823059398983680, coefficient := (-337566384192882823059398983680) }, { argument := 92809012455050507809921695744, coefficient := (-92809012455050507809921695744) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 9903520314283042199192993792, coefficient := (-9903520314283042199192993792) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 113817907496076203434505666560, coefficient := (-113817907496076203434505666560) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 246553186097377911295180800, coefficient := (-246553186097377911295180800) }, { argument := 20643684976843414227627540480, coefficient := (-20643684976843414227627540480) }, { argument := 20643692447774764079995944960, coefficient := (-20643692447774764079995944960) }, { argument := 246545715166028058926776320, coefficient := (-246545715166028058926776320) }, { argument := 1901227928066671877931663360, coefficient := (-1901227928066671877931663360) }, { argument := 280801415479611922147191029760, coefficient := (-280801415479611922147191029760) }, { argument := 2926746192756245231173002854400, coefficient := (-2926746192756245231173002854400) }, { argument := 280801415479611922147191029760, coefficient := (-280801415479611922147191029760) }, { argument := 1901227928066671877931663360, coefficient := (-1901227928066671877931663360) }, { argument := 5612903501243779524996366336, coefficient := (-5612903501243779524996366336) }, { argument := 210891203681900930114783281152, coefficient := (-210891203681900930114783281152) }, { argument := 210875253534005214469165154304, coefficient := (-210875253534005214469165154304) }, { argument := 5628853649139495170614493184, coefficient := (-5628853649139495170614493184) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 113817907496076203434505666560, coefficient := (-113817907496076203434505666560) }, { argument := 10920055046429352527946317824, coefficient := (-10920055046429352527946317824) }, { argument := 73936641647037239697342464, coefficient := (-73936641647037239697342464) }, { argument := 5612903501243779524996366336, coefficient := (-5612903501243779524996366336) }, { argument := 210891203681900930114783281152, coefficient := (-210891203681900930114783281152) }, { argument := 210875253534005214469165154304, coefficient := (-210875253534005214469165154304) }, { argument := 5628853649139495170614493184, coefficient := (-5628853649139495170614493184) }, { argument := 4467514574699636245508653056, coefficient := (-4467514574699636245508653056) }, { argument := 16249313524812682476461752320, coefficient := (-16249313524812682476461752320) }, { argument := 4467514574699636245508653056, coefficient := (-4467514574699636245508653056) }, { argument := 260250585325010017478246400, coefficient := (-260250585325010017478246400) }, { argument := 21790556364445826129162403840, coefficient := (-21790556364445826129162403840) }, { argument := 21790564250428917639995719680, coefficient := (-21790564250428917639995719680) }, { argument := 260242699341918506644930560, coefficient := (-260242699341918506644930560) }, { argument := 1922352682822968232130904064, coefficient := (-1922352682822968232130904064) }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
