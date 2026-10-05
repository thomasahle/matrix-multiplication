import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 19, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

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
def constantNumerator : ℤ := (-1534395190186821642387544499814400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    11148546711, 88331955561, 135, 1269, 14985, 1053,
    44165969289, 14985, 135, 1053, 1053, 1053,
    1053, 1053, 5574281847, 1269, 15725860275709, 814788970178465,
    210976510017, 24622207783687619, 6955269561, 16228962309, 210976510017, 210976510017,
    6955269561, 2603589239001, 104329043415, 814788970178465, 210976510017, 16228962309,
    104329043415, 16228962309, 210976510017, 210976510017, 72397948781889, 53561705,
    4484675223, 2242338423, 26780041, 57311283, 4232288289, 44112433035,
    4232288289, 57311283, 331831131381, 829507833, 10672410477035, 13053833793,
    392924763, 85378251212365, 392924763, 392924763, 33660554697, 392924763,
    13053833793, 33660554697, 2655681654963, 392924763, 392924763, 829507833,
    3219735, 237769005, 2478226575, 237769005
  ]
def negativeCoefficients : Array ℕ := #[
    25706798496451670404730191872, 203679622220506527720718467072, 20890238162940792138922721280, 24546029841455430763234197504, 289852054510803490927552757760, 651775430683752714734388903936,
    203679583060374702244554080256, 289852054510803490927552757760, 20890238162940792138922721280, 20367982208867272335449653248, 20367982208867272335449653248, 20367982208867272335449653248,
    651775430683752714734388903936, 20367982208867272335449653248, 25706837656583495880894578688, 24546029841455430763234197504, 17705744619440884472313020416, 917370825620331287931948892160,
    486478710731002325357700317184, 6930535362478405444246452568064, 256604155110858369419446321152, 18710719643500089436834627584, 486478710731002325357700317184, 486478710731002325357700317184,
    256604155110858369419446321152, 6003468045614457267875796221952, 481132790832859442661461852160, 917370825620331287931948892160, 486478710731002325357700317184, 18710719643500089436834627584,
    481132790832859442661461852160, 18710719643500089436834627584, 486478710731002325357700317184, 486478710731002325357700317184, 20378210947281472199206109184, 123504883035816157417308160,
    10340957011548413978839351296, 10340960753931617932664635392, 123501140652612203592024064, 264301642509235243116920832, 39035969456670544045918912512, 406865381332647849850338017280,
    39035969456670544045918912512, 264301642509235243116920832, 47821905908396854455652319232, 7650859351244201216194904064, 1538056443120633710657425899520, 60200182790053056937954639872,
    7248182543283980099553067008, 1538037841382206449396125532160, 7248182543283980099553067008, 7248182543283980099553067008, 310463818937330480930856370176, 7248182543283980099553067008,
    60200182790053056937954639872, 310463818937330480930856370176, 47840507646824115716952686592, 7248182543283980099553067008, 7248182543283980099553067008, 7650859351244201216194904064,
    14848406882541305793085440, 2193031991947783373366231040, 22857605692845384823052697600, 2193031991947783373366231040
  ]
def negativeScales : Array ℕ := #[
    33, 36, 7, 10, 13, 10,
    35, 13, 7, 10, 10, 10,
    10, 10, 32, 10, 43, 49,
    37, 54, 32, 33, 37, 37,
    32, 41, 36, 49, 37, 33,
    36, 33, 37, 37, 46, 25,
    32, 31, 24, 25, 31, 35,
    31, 25, 38, 29, 43, 33,
    28, 46, 28, 28, 34, 28,
    33, 34, 41, 28, 28, 29,
    21, 27, 31, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33376136606150702, 36362216400215882, 7076815597050831, 10309476353841107, 13871231465984517, 10040289721025717,
    35362216122838436, 13871231465984517, 7076815597050831, 10040289721025717, 10040289721025717, 10040289721025717,
    10040289721025717, 10040289721025717, 32376138803860578, 10309476353841107, 43838204176125815, 49533419779055931,
    37618291422946842, 54450809647029657, 32695459283525025, 33917851710790743, 37618291422946842, 37618291422946842,
    32695459283525025, 41243638995139440, 36602349879074547, 49533419779055931, 37618291422946842, 33917851710790743,
    36602349879074547, 33917851710790743, 37618291422946842, 37618291422946842, 46041014056201676, 25674698550153947,
    32062356363961776, 31062356886071742, 24674654833667892, 25772315858106994, 31978790773050458, 35360466283793122,
    31978790773050458, 25772315858106994, 38271658285636784, 29627680363651720, 43278951294469415, 33603754524400563,
    28549677851639816, 46278933845956269, 28549677851639816, 28549677851639816, 34970339914747975, 28549677851639816,
    33603754524400563, 34970339914747975, 41272219355238141, 28549677851639816, 28549677851639816, 29627680363651720,
    21618510521673872, 27824985421223289, 31206660947714085, 27824985421223289
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
noncomputable def negativeCeiling : ℝ := 1666719399 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25706798496451670404730191872, coefficient := (-25706798496451670404730191872) }, { argument := 203679622220506527720718467072, coefficient := (-203679622220506527720718467072) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 24546029841455430763234197504, coefficient := (-24546029841455430763234197504) }, { argument := 289852054510803490927552757760, coefficient := (-289852054510803490927552757760) }, { argument := 651775430683752714734388903936, coefficient := (-651775430683752714734388903936) }, { argument := 203679583060374702244554080256, coefficient := (-203679583060374702244554080256) }, { argument := 289852054510803490927552757760, coefficient := (-289852054510803490927552757760) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 651775430683752714734388903936, coefficient := (-651775430683752714734388903936) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 25706837656583495880894578688, coefficient := (-25706837656583495880894578688) }, { argument := 24546029841455430763234197504, coefficient := (-24546029841455430763234197504) }, { argument := 17705744619440884472313020416, coefficient := (-17705744619440884472313020416) }, { argument := 917370825620331287931948892160, coefficient := (-917370825620331287931948892160) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 6930535362478405444246452568064, coefficient := (-6930535362478405444246452568064) }, { argument := 256604155110858369419446321152, coefficient := (-256604155110858369419446321152) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 256604155110858369419446321152, coefficient := (-256604155110858369419446321152) }, { argument := 6003468045614457267875796221952, coefficient := (-6003468045614457267875796221952) }, { argument := 481132790832859442661461852160, coefficient := (-481132790832859442661461852160) }, { argument := 917370825620331287931948892160, coefficient := (-917370825620331287931948892160) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 481132790832859442661461852160, coefficient := (-481132790832859442661461852160) }, { argument := 18710719643500089436834627584, coefficient := (-18710719643500089436834627584) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 486478710731002325357700317184, coefficient := (-486478710731002325357700317184) }, { argument := 20378210947281472199206109184, coefficient := (-20378210947281472199206109184) }, { argument := 123504883035816157417308160, coefficient := (-123504883035816157417308160) }, { argument := 10340957011548413978839351296, coefficient := (-10340957011548413978839351296) }, { argument := 10340960753931617932664635392, coefficient := (-10340960753931617932664635392) }, { argument := 123501140652612203592024064, coefficient := (-123501140652612203592024064) }, { argument := 264301642509235243116920832, coefficient := (-264301642509235243116920832) }, { argument := 39035969456670544045918912512, coefficient := (-39035969456670544045918912512) }, { argument := 406865381332647849850338017280, coefficient := (-406865381332647849850338017280) }, { argument := 39035969456670544045918912512, coefficient := (-39035969456670544045918912512) }, { argument := 264301642509235243116920832, coefficient := (-264301642509235243116920832) }, { argument := 47821905908396854455652319232, coefficient := (-47821905908396854455652319232) }, { argument := 7650859351244201216194904064, coefficient := (-7650859351244201216194904064) }, { argument := 1538056443120633710657425899520, coefficient := (-1538056443120633710657425899520) }, { argument := 60200182790053056937954639872, coefficient := (-60200182790053056937954639872) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 1538037841382206449396125532160, coefficient := (-1538037841382206449396125532160) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 310463818937330480930856370176, coefficient := (-310463818937330480930856370176) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 60200182790053056937954639872, coefficient := (-60200182790053056937954639872) }, { argument := 310463818937330480930856370176, coefficient := (-310463818937330480930856370176) }, { argument := 47840507646824115716952686592, coefficient := (-47840507646824115716952686592) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 7248182543283980099553067008, coefficient := (-7248182543283980099553067008) }, { argument := 7650859351244201216194904064, coefficient := (-7650859351244201216194904064) }, { argument := 14848406882541305793085440, coefficient := (-14848406882541305793085440) }, { argument := 2193031991947783373366231040, coefficient := (-2193031991947783373366231040) }, { argument := 22857605692845384823052697600, coefficient := (-22857605692845384823052697600) }, { argument := 2193031991947783373366231040, coefficient := (-2193031991947783373366231040) }] }

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
def constantNumerator : ℤ := (-11525480513378808596961795464232960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3219735, 414237411, 15563963677, 31125573083, 830829093, 15847482906109,
    28045947, 1575615, 57568430539183, 85188251, 3961870407189, 85188251,
    85188251, 28045947, 1575615, 11148546711, 88331955561, 135,
    1269, 14985, 1053, 44165969289, 14985, 135,
    1053, 1053, 1053, 1053, 1053, 5574281847,
    1269, 57129485003183, 2950647562840571, 383683522495, 89082987907112849, 12648907335,
    29514117115, 383683522495, 383683522495, 12648907335, 4734907645735, 189733610025,
    2950647562840571, 383683522495, 29514117115, 189733610025, 29514117115, 383683522495,
    383683522495, 263051615914459, 10674451832395, 31166740231, 333711663801045, 490466069951,
    14763192741, 2669691742727859, 14763192741, 14763192741, 1264713511479, 14763192741,
    490466069951, 1264713511479, 85397182339661, 14763192741
  ]
def negativeCoefficients : Array ℕ := #[
    14848406882541305793085440, 7641331506473037827382706176, 287104454722130471999380652032, 287082740404821893869484376064, 7663045823781615957278982144, 17842679527678199362031190016,
    258678203306911089008050176, 14532483331848937584721920, 64816290581142210231446536192, 392861466070982946040315904, 17842678089506575656884895744, 392861466070982946040315904,
    392861466070982946040315904, 258678203306911089008050176, 14532483331848937584721920, 25706798496451670404730191872, 203679622220506527720718467072, 20890238162940792138922721280,
    24546029841455430763234197504, 289852054510803490927552757760, 651775430683752714734388903936, 203679583060374702244554080256, 289852054510803490927552757760, 20890238162940792138922721280,
    20367982208867272335449653248, 20367982208867272335449653248, 20367982208867272335449653248, 651775430683752714734388903936, 20367982208867272335449653248, 25706837656583495880894578688,
    24546029841455430763234197504, 64322081843050824572120072192, 3322133816127614433877299298304, 1769427936191161671388474900480, 25074631946470239255683812818944, 933324625683250112380734013440,
    68054920622736987361095188480, 1769427936191161671388474900480, 1769427936191161671388474900480, 933324625683250112380734013440, 21835907388381039087574256189440, 1749983673156093960713876275200,
    3322133816127614433877299298304, 1769427936191161671388474900480, 68054920622736987361095188480, 1749983673156093960713876275200, 68054920622736987361095188480, 1769427936191161671388474900480,
    1769427936191161671388474900480, 74042447463222774237289775104, 1538350633432269767128320573440, 287462440326522155879679131648, 48092919191794384025659102986240, 2261875517306055910737475272704,
    272332838204073621359696019456, 48092890950973103467289175392256, 272332838204073621359696019456, 272332838204073621359696019456, 11664923236407820114906979500032, 272332838204073621359696019456,
    2261875517306055910737475272704, 11664923236407820114906979500032, 1538378874253550325498248167424, 272332838204073621359696019456
  ]
def negativeScales : Array ℕ := #[
    21, 28, 33, 34, 29, 43,
    24, 20, 45, 26, 41, 26,
    26, 24, 20, 33, 36, 7,
    10, 13, 10, 35, 13, 7,
    10, 10, 10, 10, 10, 32,
    10, 45, 51, 38, 56, 33,
    34, 38, 38, 33, 42, 37,
    51, 38, 34, 37, 34, 38,
    38, 47, 43, 34, 48, 38,
    33, 51, 33, 33, 40, 33,
    38, 40, 46, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21618510521673872, 28625882612588771, 33857490469352804, 34857381351144109, 29629976494783738, 43849318947076972,
    24741288962308597, 20587483626047870, 45710343114907815, 26344151134652641, 41849318830791566, 26344151134652641,
    26344151134652641, 24741288962308597, 20587483626047870, 33376136606150702, 36362216400215882, 7076815597050831,
    10309476353841107, 13871231465984517, 10040289721025717, 35362216122838436, 13871231465984517, 7076815597050831,
    10040289721025717, 10040289721025717, 10040289721025717, 10040289721025717, 10040289721025717, 32376138803860578,
    10309476353841107, 45699300758335311, 51389953033098614, 38481125852681002, 56305999466158285, 33558293713205025,
    34780686134973257, 38481125852681002, 38481125852681002, 33558293713205025, 42106473424882764, 37465184308811919,
    51389953033098614, 38481125852681002, 34780686134973257, 37465184308811919, 34780686134973257, 38481125852681002,
    38481125852681002, 47902339245489322, 43279227218230093, 34859288220484159, 48245595440516726, 38835362380479145,
    33781285706855895, 51245594593346177, 33781285706855895, 33781285706855895, 40201947754889655, 33781285706855895,
    38835362380479145, 40201947754889655, 46279253702776564, 33781285706855895
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
noncomputable def negativeCeiling : ℝ := 56842531237 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14848406882541305793085440, coefficient := (-14848406882541305793085440) }, { argument := 7641331506473037827382706176, coefficient := (-7641331506473037827382706176) }, { argument := 287104454722130471999380652032, coefficient := (-287104454722130471999380652032) }, { argument := 287082740404821893869484376064, coefficient := (-287082740404821893869484376064) }, { argument := 7663045823781615957278982144, coefficient := (-7663045823781615957278982144) }, { argument := 17842679527678199362031190016, coefficient := (-17842679527678199362031190016) }, { argument := 258678203306911089008050176, coefficient := (-258678203306911089008050176) }, { argument := 14532483331848937584721920, coefficient := (-14532483331848937584721920) }, { argument := 64816290581142210231446536192, coefficient := (-64816290581142210231446536192) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 17842678089506575656884895744, coefficient := (-17842678089506575656884895744) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 392861466070982946040315904, coefficient := (-392861466070982946040315904) }, { argument := 258678203306911089008050176, coefficient := (-258678203306911089008050176) }, { argument := 14532483331848937584721920, coefficient := (-14532483331848937584721920) }, { argument := 25706798496451670404730191872, coefficient := (-25706798496451670404730191872) }, { argument := 203679622220506527720718467072, coefficient := (-203679622220506527720718467072) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 24546029841455430763234197504, coefficient := (-24546029841455430763234197504) }, { argument := 289852054510803490927552757760, coefficient := (-289852054510803490927552757760) }, { argument := 651775430683752714734388903936, coefficient := (-651775430683752714734388903936) }, { argument := 203679583060374702244554080256, coefficient := (-203679583060374702244554080256) }, { argument := 289852054510803490927552757760, coefficient := (-289852054510803490927552757760) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 651775430683752714734388903936, coefficient := (-651775430683752714734388903936) }, { argument := 20367982208867272335449653248, coefficient := (-20367982208867272335449653248) }, { argument := 25706837656583495880894578688, coefficient := (-25706837656583495880894578688) }, { argument := 24546029841455430763234197504, coefficient := (-24546029841455430763234197504) }, { argument := 64322081843050824572120072192, coefficient := (-64322081843050824572120072192) }, { argument := 3322133816127614433877299298304, coefficient := (-3322133816127614433877299298304) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 25074631946470239255683812818944, coefficient := (-25074631946470239255683812818944) }, { argument := 933324625683250112380734013440, coefficient := (-933324625683250112380734013440) }, { argument := 68054920622736987361095188480, coefficient := (-68054920622736987361095188480) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 933324625683250112380734013440, coefficient := (-933324625683250112380734013440) }, { argument := 21835907388381039087574256189440, coefficient := (-21835907388381039087574256189440) }, { argument := 1749983673156093960713876275200, coefficient := (-1749983673156093960713876275200) }, { argument := 3322133816127614433877299298304, coefficient := (-3322133816127614433877299298304) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 68054920622736987361095188480, coefficient := (-68054920622736987361095188480) }, { argument := 1749983673156093960713876275200, coefficient := (-1749983673156093960713876275200) }, { argument := 68054920622736987361095188480, coefficient := (-68054920622736987361095188480) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 1769427936191161671388474900480, coefficient := (-1769427936191161671388474900480) }, { argument := 74042447463222774237289775104, coefficient := (-74042447463222774237289775104) }, { argument := 1538350633432269767128320573440, coefficient := (-1538350633432269767128320573440) }, { argument := 287462440326522155879679131648, coefficient := (-287462440326522155879679131648) }, { argument := 48092919191794384025659102986240, coefficient := (-48092919191794384025659102986240) }, { argument := 2261875517306055910737475272704, coefficient := (-2261875517306055910737475272704) }, { argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }, { argument := 48092890950973103467289175392256, coefficient := (-48092890950973103467289175392256) }, { argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }, { argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }, { argument := 11664923236407820114906979500032, coefficient := (-11664923236407820114906979500032) }, { argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }, { argument := 2261875517306055910737475272704, coefficient := (-2261875517306055910737475272704) }, { argument := 11664923236407820114906979500032, coefficient := (-11664923236407820114906979500032) }, { argument := 1538378874253550325498248167424, coefficient := (-1538378874253550325498248167424) }, { argument := 272332838204073621359696019456, coefficient := (-272332838204073621359696019456) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
