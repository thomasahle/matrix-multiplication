import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-35768391892614320701924621762428928)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    903967763301, 10552152879, 350565967869, 903967763301, 376462995347371, 10552152879,
    10552152879, 22276767189, 314337923, 32957764297, 355251757875, 16478894719,
    314337923, 9757554937, 353617020679, 2828937205055, 78059399873, 4975607844231341,
    10150430331, 570248895, 17982577555792205, 30831456923, 2487803754328323, 30831456923,
    30831456923, 10150430331, 570248895, 293705667, 10643990589, 85151956005,
    2349614043, 44436116725, 76270709515, 44436116725, 26884500777, 26884490967,
    49594306821619, 4990299742022919, 44225352535, 187758801454305285, 1457978655, 3401950195,
    44225352535, 44225352535, 1457978655, 545770009855, 21869679825, 4990299742975239,
    44225352535, 3401950195, 21869679825, 3401950195, 44225352535, 44225352535,
    214291870248951, 1503780322587237, 178214203005, 53218989955711131, 2804528773605, 84417254055,
    106433945411224549, 84417254055, 84417254055, 7231744764045
  ]
def negativeCoefficients : Array ℕ := #[
    16675261980497200452235130044416, 389305727171140866589147004928, 3233400345115864419726526513152, 16675261980497200452235130044416, 6781754422260803219819346264064, 389305727171140866589147004928,
    389305727171140866589147004928, 410933823125093136955210727424, 362406951140151210014670848, 37997715201775062287355215872, 409577391203472298985127936000, 37997744187374609608095039488,
    362406951140151210014670848, 89997559354000063637378564096, 3261541340286585607017444933632, 3261542538890298990901518663680, 89996360750286679753304834048, 5602036408305496058291535478784,
    23405298819246991550932058112, 1314904428047583794996183040, 20246582394856704795404580945920, 35546249704886348591396814848, 5602036030481978219049573679104, 35546249704886348591396814848,
    35546249704886348591396814848, 23405298819246991550932058112, 1314904428047583794996183040, 10835826544294322043296415744, 392693940636511979440227483648, 392694084950002554088477163520,
    10835682230803747395046735872, 819701672855559639355988377600, 2813892517486897919569669652480, 819701672855559639355988377600, 123982876345691146423168401408, 123982831105051305650493063168,
    55838225430385344059073888256, 5618578014660375081767934099456, 815813759782726945414378946560, 52849404266571263998358936616960, 430319345819460366811980103680, 31377452299335651746706882560,
    815813759782726945414378946560, 815813759782726945414378946560, 430319345819460366811980103680, 10067679694901124831871951175680, 806848773411488187772462694400, 5618578015732592081052301787136,
    815813759782726945414378946560, 31377452299335651746706882560, 806848773411488187772462694400, 31377452299335651746706882560, 815813759782726945414378946560, 815813759782726945414378946560,
    60317799187606400093814521856, 6772424500450964822557879959552, 410933974141669339387668725760, 239677023333574818993979288190976, 3233401533377871907287182868480, 389305870239476216262001950720,
    239667938446781295764360136753152, 389305870239476216262001950720, 389305870239476216262001950720, 16675268108590897929889083555840
  ]
def negativeScales : Array ℕ := #[
    39, 33, 38, 39, 48, 33,
    33, 34, 28, 34, 38, 33,
    28, 33, 38, 41, 36, 52,
    33, 29, 53, 34, 51, 34,
    34, 33, 29, 28, 33, 36,
    31, 35, 36, 35, 34, 34,
    45, 52, 35, 57, 30, 31,
    35, 35, 30, 38, 34, 52,
    35, 31, 34, 31, 35, 35,
    47, 50, 37, 55, 41, 36,
    56, 36, 36, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39717480368993439, 33296818320412095, 38350894993167888, 39717480368993439, 48419501389727789, 33296818320412095,
    33296818320412095, 34374820832413370, 28227741094307803, 34939899337704807, 38370050832064429, 33939900438228110,
    28227741094307803, 33183872534337073, 38363396761528247, 41363397291712947, 36183853320136589, 52143794206311602,
    33240821841135225, 29087016505056190, 53997449367145370, 34843684015199587, 51143794109010532, 34843684015199587,
    34843684015199587, 33240821841135225, 29087016505056190, 28129795861581280, 33309320088772453, 36309320618957153,
    31129776647380797, 35371013693900046, 36150410069491655, 35371013693900046, 34646055631098297, 34646055104667062,
    45495239749478039, 52148047896857465, 35364154592037389, 57381658150741410, 30441322452559881, 31663714873926383,
    35364154592037389, 35364154592037389, 30441322452559881, 38989502184246767, 34348213048168367, 52148047897132781,
    35364154592037389, 31663714873926383, 34348213048168367, 31663714873926383, 35364154592037389, 35364154592037389,
    47606570446881078, 50417515251854062, 37374821362598070, 55562790647881292, 41350895523352588, 36296818850596794,
    56562735961915353, 36296818850596794, 36296818850596794, 42717480899178140
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
noncomputable def negativeCeiling : ℝ := 109480074651 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16675261980497200452235130044416, coefficient := (-16675261980497200452235130044416) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }, { argument := 3233400345115864419726526513152, coefficient := (-3233400345115864419726526513152) }, { argument := 16675261980497200452235130044416, coefficient := (-16675261980497200452235130044416) }, { argument := 6781754422260803219819346264064, coefficient := (-6781754422260803219819346264064) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }, { argument := 389305727171140866589147004928, coefficient := (-389305727171140866589147004928) }, { argument := 410933823125093136955210727424, coefficient := (-410933823125093136955210727424) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 37997715201775062287355215872, coefficient := (-37997715201775062287355215872) }, { argument := 409577391203472298985127936000, coefficient := (-409577391203472298985127936000) }, { argument := 37997744187374609608095039488, coefficient := (-37997744187374609608095039488) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 89997559354000063637378564096, coefficient := (-89997559354000063637378564096) }, { argument := 3261541340286585607017444933632, coefficient := (-3261541340286585607017444933632) }, { argument := 3261542538890298990901518663680, coefficient := (-3261542538890298990901518663680) }, { argument := 89996360750286679753304834048, coefficient := (-89996360750286679753304834048) }, { argument := 5602036408305496058291535478784, coefficient := (-5602036408305496058291535478784) }, { argument := 23405298819246991550932058112, coefficient := (-23405298819246991550932058112) }, { argument := 1314904428047583794996183040, coefficient := (-1314904428047583794996183040) }, { argument := 20246582394856704795404580945920, coefficient := (-20246582394856704795404580945920) }, { argument := 35546249704886348591396814848, coefficient := (-35546249704886348591396814848) }, { argument := 5602036030481978219049573679104, coefficient := (-5602036030481978219049573679104) }, { argument := 35546249704886348591396814848, coefficient := (-35546249704886348591396814848) }, { argument := 35546249704886348591396814848, coefficient := (-35546249704886348591396814848) }, { argument := 23405298819246991550932058112, coefficient := (-23405298819246991550932058112) }, { argument := 1314904428047583794996183040, coefficient := (-1314904428047583794996183040) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 123982876345691146423168401408, coefficient := (-123982876345691146423168401408) }, { argument := 123982831105051305650493063168, coefficient := (-123982831105051305650493063168) }, { argument := 55838225430385344059073888256, coefficient := (-55838225430385344059073888256) }, { argument := 5618578014660375081767934099456, coefficient := (-5618578014660375081767934099456) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 52849404266571263998358936616960, coefficient := (-52849404266571263998358936616960) }, { argument := 430319345819460366811980103680, coefficient := (-430319345819460366811980103680) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 430319345819460366811980103680, coefficient := (-430319345819460366811980103680) }, { argument := 10067679694901124831871951175680, coefficient := (-10067679694901124831871951175680) }, { argument := 806848773411488187772462694400, coefficient := (-806848773411488187772462694400) }, { argument := 5618578015732592081052301787136, coefficient := (-5618578015732592081052301787136) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 806848773411488187772462694400, coefficient := (-806848773411488187772462694400) }, { argument := 31377452299335651746706882560, coefficient := (-31377452299335651746706882560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 815813759782726945414378946560, coefficient := (-815813759782726945414378946560) }, { argument := 60317799187606400093814521856, coefficient := (-60317799187606400093814521856) }, { argument := 6772424500450964822557879959552, coefficient := (-6772424500450964822557879959552) }, { argument := 410933974141669339387668725760, coefficient := (-410933974141669339387668725760) }, { argument := 239677023333574818993979288190976, coefficient := (-239677023333574818993979288190976) }, { argument := 3233401533377871907287182868480, coefficient := (-3233401533377871907287182868480) }, { argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 239667938446781295764360136753152, coefficient := (-239667938446781295764360136753152) }, { argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 16675268108590897929889083555840, coefficient := (-16675268108590897929889083555840) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-20306276637875632892369609645096960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    84417254055, 2804528773605, 7231744764045, 3011595145372187, 84417254055, 84417254055,
    178214203005, 93539160400312297, 109411493625, 6146713125, 42407675647950345, 332332289625,
    93539153405034447, 332332289625, 332332289625, 109411493625, 6146713125, 293705667,
    10643990589, 85151956005, 2349614043, 1464926925, 2514418995, 1464926925,
    546560750823, 546560743193, 3418162825, 5866977655, 3418162825, 2285896225,
    2285895135, 1816587, 314337923, 32957764297, 355251757875, 16478894719,
    314337923, 293705667, 10643990589, 85151956005, 2349614043, 314337923,
    32957764297, 355251757875, 16478894719, 314337923, 25160785473, 911835193791,
    7294684231095, 201283603017, 44436116725, 76270709515, 44436116725, 293705667,
    10643990589, 85151956005, 2349614043, 44436116725, 76270709515, 44436116725,
    21487424515, 21487414269, 103487331, 10850460009
  ]
def negativeCoefficients : Array ℕ := #[
    389305870239476216262001950720, 3233401533377871907287182868480, 16675268108590897929889083555840, 6781509387244488052177031397376, 389305870239476216262001950720, 389305870239476216262001950720,
    410933974141669339387668725760, 52657865990424439528048415473664, 252285727702834892091949056000, 14173355488923308544491520000, 190987192245758031253384326021120, 383153043383893440986087424000,
    52657862052433099701412863934464, 383153043383893440986087424000, 383153043383893440986087424000, 252285727702834892091949056000, 14173355488923308544491520000, 10835826544294322043296415744,
    392693940636511979440227483648, 392694084950002554088477163520, 10835682230803747395046735872, 432370113154580908671290572800, 1484250998234847254278507069440, 432370113154580908671290572800,
    2520566572791604546516908244992, 2520566537604440225915938537472, 31526987417521524590614937600, 108226635287957612291141140480, 31526987417521524590614937600, 84334685283267571570914099200,
    84334645069365490884091576320, 8578589562016720189812375552, 362406951140151210014670848, 37997715201775062287355215872, 409577391203472298985127936000, 37997744187374609608095039488,
    362406951140151210014670848, 10835826544294322043296415744, 392693940636511979440227483648, 392694084950002554088477163520, 10835682230803747395046735872, 362406951140151210014670848,
    37997715201775062287355215872, 409577391203472298985127936000, 37997744187374609608095039488, 362406951140151210014670848, 464134570313940127521196474368, 16820390457263929786023077216256,
    16820396638691776066789771837440, 464128388886093846754501853184, 819701672855559639355988377600, 2813892517486897919569669652480, 819701672855559639355988377600, 10835826544294322043296415744,
    392693940636511979440227483648, 392694084950002554088477163520, 10835682230803747395046735872, 819701672855559639355988377600, 2813892517486897919569669652480, 819701672855559639355988377600,
    99093255207839396595824066560, 99093207956504451788807602176, 238625538728533595743322112, 25019457358505404761341165568
  ]
def negativeScales : Array ℕ := #[
    36, 41, 42, 51, 36, 36,
    37, 56, 36, 32, 55, 38,
    56, 38, 38, 36, 32, 28,
    33, 36, 31, 30, 31, 30,
    38, 38, 31, 32, 31, 31,
    31, 20, 28, 34, 38, 33,
    28, 28, 33, 36, 31, 28,
    34, 38, 33, 28, 34, 39,
    42, 37, 35, 36, 35, 28,
    33, 36, 31, 35, 36, 35,
    34, 34, 26, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36296818850596794, 41350895523352588, 42717480899178140, 51419449262038188, 36296818850596794, 36296818850596794,
    37374821362598070, 56376419997502634, 36670973344311412, 32517168008196845, 55235174929614316, 38273835516805124,
    56376419889611426, 38273835516805124, 38273835516805124, 36670973344311412, 32517168008196845, 28129795861581280,
    33309320088772453, 36309320618957153, 31129776647380797, 30448181554422547, 31227577930014115, 30448181554422547,
    38991590926388948, 38991590906248886, 31670573975794607, 32449970351350610, 31670573975794607, 31090112763629550,
    31090112075698947, 20792799030852688, 28227741094307803, 34939899337704807, 38370050832064429, 33939900438228110,
    28227741094307803, 28129795861581280, 33309320088772453, 36309320618957153, 31129776647380797, 28227741094307803,
    34939899337704807, 38370050832064429, 33939900438228110, 28227741094307803, 34550457910055350, 39729982137389450,
    42729982667574152, 37550438695854866, 35371013693900046, 36150410069491655, 35371013693900046, 28129795861581280,
    33309320088772453, 36309320618957153, 31129776647380797, 35371013693900046, 36150410069491655, 35371013693900046,
    34322773520419825, 34322772832489222, 26624878921789179, 33337037156394529
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
noncomputable def negativeCeiling : ℝ := 120074475191 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 3233401533377871907287182868480, coefficient := (-3233401533377871907287182868480) }, { argument := 16675268108590897929889083555840, coefficient := (-16675268108590897929889083555840) }, { argument := 6781509387244488052177031397376, coefficient := (-6781509387244488052177031397376) }, { argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 389305870239476216262001950720, coefficient := (-389305870239476216262001950720) }, { argument := 410933974141669339387668725760, coefficient := (-410933974141669339387668725760) }, { argument := 52657865990424439528048415473664, coefficient := (-52657865990424439528048415473664) }, { argument := 252285727702834892091949056000, coefficient := (-252285727702834892091949056000) }, { argument := 14173355488923308544491520000, coefficient := (-14173355488923308544491520000) }, { argument := 190987192245758031253384326021120, coefficient := (-190987192245758031253384326021120) }, { argument := 383153043383893440986087424000, coefficient := (-383153043383893440986087424000) }, { argument := 52657862052433099701412863934464, coefficient := (-52657862052433099701412863934464) }, { argument := 383153043383893440986087424000, coefficient := (-383153043383893440986087424000) }, { argument := 383153043383893440986087424000, coefficient := (-383153043383893440986087424000) }, { argument := 252285727702834892091949056000, coefficient := (-252285727702834892091949056000) }, { argument := 14173355488923308544491520000, coefficient := (-14173355488923308544491520000) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 432370113154580908671290572800, coefficient := (-432370113154580908671290572800) }, { argument := 1484250998234847254278507069440, coefficient := (-1484250998234847254278507069440) }, { argument := 432370113154580908671290572800, coefficient := (-432370113154580908671290572800) }, { argument := 2520566572791604546516908244992, coefficient := (-2520566572791604546516908244992) }, { argument := 2520566537604440225915938537472, coefficient := (-2520566537604440225915938537472) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 108226635287957612291141140480, coefficient := (-108226635287957612291141140480) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 84334685283267571570914099200, coefficient := (-84334685283267571570914099200) }, { argument := 84334645069365490884091576320, coefficient := (-84334645069365490884091576320) }, { argument := 8578589562016720189812375552, coefficient := (-8578589562016720189812375552) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 37997715201775062287355215872, coefficient := (-37997715201775062287355215872) }, { argument := 409577391203472298985127936000, coefficient := (-409577391203472298985127936000) }, { argument := 37997744187374609608095039488, coefficient := (-37997744187374609608095039488) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 37997715201775062287355215872, coefficient := (-37997715201775062287355215872) }, { argument := 409577391203472298985127936000, coefficient := (-409577391203472298985127936000) }, { argument := 37997744187374609608095039488, coefficient := (-37997744187374609608095039488) }, { argument := 362406951140151210014670848, coefficient := (-362406951140151210014670848) }, { argument := 464134570313940127521196474368, coefficient := (-464134570313940127521196474368) }, { argument := 16820390457263929786023077216256, coefficient := (-16820390457263929786023077216256) }, { argument := 16820396638691776066789771837440, coefficient := (-16820396638691776066789771837440) }, { argument := 464128388886093846754501853184, coefficient := (-464128388886093846754501853184) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 99093255207839396595824066560, coefficient := (-99093255207839396595824066560) }, { argument := 99093207956504451788807602176, coefficient := (-99093207956504451788807602176) }, { argument := 238625538728533595743322112, coefficient := (-238625538728533595743322112) }, { argument := 25019457358505404761341165568, coefficient := (-25019457358505404761341165568) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
