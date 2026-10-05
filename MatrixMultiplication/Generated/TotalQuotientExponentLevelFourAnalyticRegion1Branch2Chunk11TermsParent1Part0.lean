import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16059605468406412984642453326790656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    44088411, 2773, 679345557, 68617, 2183, 2717374761,
    1121, 1121, 37937, 2065, 68617, 37937,
    88184781, 2183, 2065, 2773, 2238291718817771, 2789212825,
    910164185, 3825746293730325, 9189722255, 2238291449333739, 18408804645, 8250197935,
    2789212825, 910164185, 2244043541081323, 10604033139, 2243977635819797, 5354099247,
    1514861877, 2754939595, 1514861877, 11555310275, 11555304765, 87956883,
    3770680195, 3770678397, 1363, 2238225813587989, 2789211495, 910163751,
    3825633165558763, 9189717873, 2238225544103957, 18408795867, 8250194001, 2789211495,
    910163751, 3836136034320917, 19284577165, 3836022905823211, 9737006545, 1358627005,
    38071706485, 38071688331, 33727, 1073, 2244043267927275, 10604033139,
    2243977362665749, 5354099247, 679311635, 551
  ]
def negativeCoefficients : Array ℕ := #[
    416403268778762755211224154112, 53637620764661867223363616768, 12832474754652840344362772594688, 1327245807431952161293018857472, 42225361027499767814137315328, 12832439492742312756721961926656,
    43366587001215977755059945472, 43366587001215977755059945472, 733808301099522992013251182592, 39942909080067347932292055040, 1327245807431952161293018857472, 733808301099522992013251182592,
    416440854093599914717479960576, 42225361027499767814137315328, 39942909080067347932292055040, 53637620764661867223363616768, 10080369750814180485226525884416, 205807580599533706769386700800,
    8394782892875716986646036480, 34459259165715895614861370982400, 169520454546458026891626414080, 10080368537165994387727705964544, 169791253994615308084744028160, 152189289864392030532099112960,
    205807580599533706769386700800, 8394782892875716986646036480, 10106273655417014595262986846208, 24451235683033492999611875328, 10105976844505764346576410509312, 24691424638662505700983308288,
    27944269352038277713842143232, 101639331294988084553229271040, 27944269352038277713842143232, 213157851335231339154007654400, 213157749693671493014378250240, 415364636216886888312569069568,
    8694596567621278307597680640, 8694592421715547741375954944, 52728508548311666083984572416, 10080072940045892503111198572544, 205807482462855234634572103680, 8394778889932252991673335808,
    34458240197733312157376520912896, 169520373712825495896371232768, 10080071726397706405612378652672, 169791173031855568573521985536, 152189217294900844558723055616, 205807482462855234634572103680,
    8394778889932252991673335808, 34552841629420428111339442929664, 88934414883114573984075612160, 34551822658500200660116346765312, 89808033889824933257003663360, 12831869262267139764192762920960,
    175574756494545813566327357440, 175574672773997835035527348224, 1304750115780563141610086334464, 41509676942287907342711259136, 10106272425240545807720408678400, 24451235683033492999611875328,
    10105975614329295559033832341504, 24691424638662505700983308288, 12831833986189512727943016611840, 42631560102890283216838590464
  ]
def negativeScales : Array ℕ := #[
    25, 11, 29, 16, 11, 31,
    10, 10, 15, 11, 16, 15,
    26, 11, 11, 11, 50, 31,
    29, 51, 33, 50, 34, 32,
    31, 29, 50, 33, 50, 32,
    30, 31, 30, 33, 33, 26,
    31, 31, 10, 50, 31, 29,
    51, 33, 50, 34, 32, 31,
    29, 51, 34, 51, 33, 30,
    35, 35, 15, 10, 50, 33,
    50, 32, 29, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25393896145616763, 11437231901039508, 29339570363843354, 16066278430835060, 11092096414990792, 31339566399506441,
    10130570562805427, 10130570562805427, 15211317976689789, 11011926066306808, 16066278430835060, 15211317976689789,
    26394026360013128, 11092096414990792, 11011926066306808, 11437231901039508, 50991319520381037, 31377210874353816,
    29761551576698605, 51764662627435708, 33097374112955484, 50991319346684541, 34099676898824904, 32941781595311034,
    31377210874353816, 29761551576698605, 50995022113944206, 33303894032810469, 50994979742830722, 32317996735928652,
    30496539110753106, 31359373540496190, 30496539110753106, 33427836947423801, 33427836259493198, 26390293143346199,
    31812177650306125, 31812176962375511, 10412569846805221, 50991277040404572, 31377210186423212, 29761550888767997,
    51764619965990395, 33097373425024880, 50991276866702961, 34099676210894301, 32941780907380324, 31377210186423212,
    29761550888767997, 51768575304732208, 34166728462553793, 51768532758709615, 33180831165671976, 30339502289563977,
    35148000186025452, 35147999498094848, 15041616376600791, 10067434360756522, 50995021938333463, 33303894032810469,
    50994979567214822, 32317996735928652, 29339498323447181, 9105908508571158
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
noncomputable def negativeCeiling : ℝ := 156845269099 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 416403268778762755211224154112, coefficient := (-416403268778762755211224154112) }, { argument := 53637620764661867223363616768, coefficient := (-53637620764661867223363616768) }, { argument := 12832474754652840344362772594688, coefficient := (-12832474754652840344362772594688) }, { argument := 1327245807431952161293018857472, coefficient := (-1327245807431952161293018857472) }, { argument := 42225361027499767814137315328, coefficient := (-42225361027499767814137315328) }, { argument := 12832439492742312756721961926656, coefficient := (-12832439492742312756721961926656) }, { argument := 43366587001215977755059945472, coefficient := (-43366587001215977755059945472) }, { argument := 43366587001215977755059945472, coefficient := (-43366587001215977755059945472) }, { argument := 733808301099522992013251182592, coefficient := (-733808301099522992013251182592) }, { argument := 39942909080067347932292055040, coefficient := (-39942909080067347932292055040) }, { argument := 1327245807431952161293018857472, coefficient := (-1327245807431952161293018857472) }, { argument := 733808301099522992013251182592, coefficient := (-733808301099522992013251182592) }, { argument := 416440854093599914717479960576, coefficient := (-416440854093599914717479960576) }, { argument := 42225361027499767814137315328, coefficient := (-42225361027499767814137315328) }, { argument := 39942909080067347932292055040, coefficient := (-39942909080067347932292055040) }, { argument := 53637620764661867223363616768, coefficient := (-53637620764661867223363616768) }, { argument := 10080369750814180485226525884416, coefficient := (-10080369750814180485226525884416) }, { argument := 205807580599533706769386700800, coefficient := (-205807580599533706769386700800) }, { argument := 8394782892875716986646036480, coefficient := (-8394782892875716986646036480) }, { argument := 34459259165715895614861370982400, coefficient := (-34459259165715895614861370982400) }, { argument := 169520454546458026891626414080, coefficient := (-169520454546458026891626414080) }, { argument := 10080368537165994387727705964544, coefficient := (-10080368537165994387727705964544) }, { argument := 169791253994615308084744028160, coefficient := (-169791253994615308084744028160) }, { argument := 152189289864392030532099112960, coefficient := (-152189289864392030532099112960) }, { argument := 205807580599533706769386700800, coefficient := (-205807580599533706769386700800) }, { argument := 8394782892875716986646036480, coefficient := (-8394782892875716986646036480) }, { argument := 10106273655417014595262986846208, coefficient := (-10106273655417014595262986846208) }, { argument := 24451235683033492999611875328, coefficient := (-24451235683033492999611875328) }, { argument := 10105976844505764346576410509312, coefficient := (-10105976844505764346576410509312) }, { argument := 24691424638662505700983308288, coefficient := (-24691424638662505700983308288) }, { argument := 27944269352038277713842143232, coefficient := (-27944269352038277713842143232) }, { argument := 101639331294988084553229271040, coefficient := (-101639331294988084553229271040) }, { argument := 27944269352038277713842143232, coefficient := (-27944269352038277713842143232) }, { argument := 213157851335231339154007654400, coefficient := (-213157851335231339154007654400) }, { argument := 213157749693671493014378250240, coefficient := (-213157749693671493014378250240) }, { argument := 415364636216886888312569069568, coefficient := (-415364636216886888312569069568) }, { argument := 8694596567621278307597680640, coefficient := (-8694596567621278307597680640) }, { argument := 8694592421715547741375954944, coefficient := (-8694592421715547741375954944) }, { argument := 52728508548311666083984572416, coefficient := (-52728508548311666083984572416) }, { argument := 10080072940045892503111198572544, coefficient := (-10080072940045892503111198572544) }, { argument := 205807482462855234634572103680, coefficient := (-205807482462855234634572103680) }, { argument := 8394778889932252991673335808, coefficient := (-8394778889932252991673335808) }, { argument := 34458240197733312157376520912896, coefficient := (-34458240197733312157376520912896) }, { argument := 169520373712825495896371232768, coefficient := (-169520373712825495896371232768) }, { argument := 10080071726397706405612378652672, coefficient := (-10080071726397706405612378652672) }, { argument := 169791173031855568573521985536, coefficient := (-169791173031855568573521985536) }, { argument := 152189217294900844558723055616, coefficient := (-152189217294900844558723055616) }, { argument := 205807482462855234634572103680, coefficient := (-205807482462855234634572103680) }, { argument := 8394778889932252991673335808, coefficient := (-8394778889932252991673335808) }, { argument := 34552841629420428111339442929664, coefficient := (-34552841629420428111339442929664) }, { argument := 88934414883114573984075612160, coefficient := (-88934414883114573984075612160) }, { argument := 34551822658500200660116346765312, coefficient := (-34551822658500200660116346765312) }, { argument := 89808033889824933257003663360, coefficient := (-89808033889824933257003663360) }, { argument := 12831869262267139764192762920960, coefficient := (-12831869262267139764192762920960) }, { argument := 175574756494545813566327357440, coefficient := (-175574756494545813566327357440) }, { argument := 175574672773997835035527348224, coefficient := (-175574672773997835035527348224) }, { argument := 1304750115780563141610086334464, coefficient := (-1304750115780563141610086334464) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 10106272425240545807720408678400, coefficient := (-10106272425240545807720408678400) }, { argument := 24451235683033492999611875328, coefficient := (-24451235683033492999611875328) }, { argument := 10105975614329295559033832341504, coefficient := (-10105975614329295559033832341504) }, { argument := 24691424638662505700983308288, coefficient := (-24691424638662505700983308288) }, { argument := 12831833986189512727943016611840, coefficient := (-12831833986189512727943016611840) }, { argument := 42631560102890283216838590464, coefficient := (-42631560102890283216838590464) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 11851300724881688347433232035217408
def positiveArguments : Array ℕ := #[
    3597, 781, 11779904291, 7635, 11779562717, 3855,
    8571549675, 5415, 1767, 29308437557, 17841, 267860895,
    35739, 16017, 5415, 1767, 176133705, 5499,
    2717318119, 136071, 4329, 5434621301, 2223, 2223,
    75231, 4095, 136071, 75231, 44037405, 4329,
    4095, 5499
  ]
def positiveCoefficients : Array ℕ := #[
    284983700563808822323977589358592, 61877194923640447660557825212416, 111258050390461423292930244739072, 295364756248246199964212920320, 111254824315243383860541798744064, 298266178215321309983507742720,
    40477998891472200498821254348800, 837930664091291773572344709120, 34178750772144796027293007872, 138405183184454706916353137180672, 690190257527827171389852352512, 40477994003822890728738458173440,
    691292797875315713197184385024, 619627675288560495720602271744, 837930664091291773572344709120, 34178750772144796027293007872, 831767904995649643523793223680, 106366129312973533307348189184,
    25664344016919980108555535515648, 2631995923212515302903105191936, 83735037969787675156848574464, 25664273478931825484664978538496, 85998147104106260971898535936, 85998147104106260971898535936,
    1455179173366850679077125226496, 79208819701150503526748651520, 2631995923212515302903105191936, 1455179173366850679077125226496, 831843061458224513927369195520, 83735037969787675156848574464,
    79208819701150503526748651520, 106366129312973533307348189184
  ]
def positiveScales : Array ℕ := #[
    11, 9, 33, 12, 33, 11,
    32, 12, 10, 34, 14, 27,
    15, 13, 12, 10, 27, 12,
    31, 17, 12, 32, 11, 11,
    16, 11, 17, 16, 25, 12,
    11, 12
  ]
def negativeArguments : Array ℕ := #[
    764871321, 1391000935, 764871321, 76265047815, 76265011449, 551,
    34179391445, 34179375147, 18647, 1015, 11555310275, 11555304765,
    33727, 18647, 87964839, 3770680195, 3770678397, 1073,
    1015, 1363, 781, 11, 11, 781
  ]
def negativeCoefficients : Array ℕ := #[
    28218771015614292229695209472, 102637753016942780865147043840, 28218771015614292229695209472, 175855227351565854802056314880, 175855143497278981736862056448, 42631560102890283216838590464,
    157624621645263174479674081280, 157624546484004446150106021888, 721370872267327687063874043904, 39265910621083155594456596480, 213157851335231339154007654400, 213157749693671493014378250240,
    1304750115780563141610086334464, 721370872267327687063874043904, 415402207364624599209889234944, 8694596567621278307597680640, 8694592421715547741375954944, 41509676942287907342711259136,
    39265910621083155594456596480, 52728508548311666083984572416, 61877194923640447660557825212416, 223106505640168374663419764146176, 223106505640168374663419764146176, 61877194923640447660557825212416
  ]
def negativeScales : Array ℕ := #[
    29, 30, 29, 36, 36, 9,
    34, 34, 14, 9, 33, 33,
    15, 14, 26, 31, 31, 10,
    9, 10, 9, 3, 3, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11812578444083777, 9609178738141526, 33455608766525813, 12898412441421818, 33455566933056850, 11912515144465203,
    32996908909481347, 12402745622495688, 10787086324520917, 34770597008354925, 14122908861097359, 27996908735278375,
    15125211646966780, 13967316333526543, 12402745622495688, 10787086324520917, 27392095769253310, 12424953571261040,
    31339536327105178, 17054000101056622, 12079818085212354, 32339532361878345, 11118292233026989, 11118292233026989,
    16199039646911351, 11999647735076951, 17054000101056622, 16199039646911351, 25392226121671162, 12079818085212354,
    11999647735076951, 12424953571261040
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29510641813871433, 30373476243614374, 29510641813871433, 36150302971894872, 36150302283964269, 9105908508571158,
    34992407680279856, 34992406992349021, 14186655922455520, 9987264031369531, 33427836947423801, 33427836259493198,
    15041616376600791, 14186655922455520, 26390423634130653, 31812177650306125, 31812176962375511, 10067434360756522,
    9987264031369531, 10412569846805221, 9609178738149255, 3459431618637364, 3459431618637364, 9609178738149255
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 24757762371 / 100000000000
noncomputable def negativeCeiling : ℝ := 34057055889 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28218771015614292229695209472, coefficient := (-28218771015614292229695209472) }, { argument := 102637753016942780865147043840, coefficient := (-102637753016942780865147043840) }, { argument := 28218771015614292229695209472, coefficient := (-28218771015614292229695209472) }, { argument := 175855227351565854802056314880, coefficient := (-175855227351565854802056314880) }, { argument := 175855143497278981736862056448, coefficient := (-175855143497278981736862056448) }, { argument := 42631560102890283216838590464, coefficient := (-42631560102890283216838590464) }, { argument := 157624621645263174479674081280, coefficient := (-157624621645263174479674081280) }, { argument := 157624546484004446150106021888, coefficient := (-157624546484004446150106021888) }, { argument := 721370872267327687063874043904, coefficient := (-721370872267327687063874043904) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 213157851335231339154007654400, coefficient := (-213157851335231339154007654400) }, { argument := 213157749693671493014378250240, coefficient := (-213157749693671493014378250240) }, { argument := 1304750115780563141610086334464, coefficient := (-1304750115780563141610086334464) }, { argument := 721370872267327687063874043904, coefficient := (-721370872267327687063874043904) }, { argument := 415402207364624599209889234944, coefficient := (-415402207364624599209889234944) }, { argument := 8694596567621278307597680640, coefficient := (-8694596567621278307597680640) }, { argument := 8694592421715547741375954944, coefficient := (-8694592421715547741375954944) }, { argument := 41509676942287907342711259136, coefficient := (-41509676942287907342711259136) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 52728508548311666083984572416, coefficient := (-52728508548311666083984572416) }, { argument := 284983700563808822323977589358592, coefficient := 284983700563808822323977589358592 }, { argument := 61877194923640447660557825212416, coefficient := 61877194923640447660557825212416 }, { argument := 61877194923640447660557825212416, coefficient := (-61877194923640447660557825212416) }, { argument := 111258050390461423292930244739072, coefficient := 111258050390461423292930244739072 }, { argument := 295364756248246199964212920320, coefficient := 295364756248246199964212920320 }, { argument := 111254824315243383860541798744064, coefficient := 111254824315243383860541798744064 }, { argument := 298266178215321309983507742720, coefficient := 298266178215321309983507742720 }, { argument := 223106505640168374663419764146176, coefficient := (-223106505640168374663419764146176) }, { argument := 40477998891472200498821254348800, coefficient := 40477998891472200498821254348800 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 138405183184454706916353137180672, coefficient := 138405183184454706916353137180672 }, { argument := 690190257527827171389852352512, coefficient := 690190257527827171389852352512 }, { argument := 40477994003822890728738458173440, coefficient := 40477994003822890728738458173440 }, { argument := 691292797875315713197184385024, coefficient := 691292797875315713197184385024 }, { argument := 619627675288560495720602271744, coefficient := 619627675288560495720602271744 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 223106505640168374663419764146176, coefficient := (-223106505640168374663419764146176) }, { argument := 831767904995649643523793223680, coefficient := 831767904995649643523793223680 }, { argument := 106366129312973533307348189184, coefficient := 106366129312973533307348189184 }, { argument := 25664344016919980108555535515648, coefficient := 25664344016919980108555535515648 }, { argument := 2631995923212515302903105191936, coefficient := 2631995923212515302903105191936 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 25664273478931825484664978538496, coefficient := 25664273478931825484664978538496 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 85998147104106260971898535936, coefficient := 85998147104106260971898535936 }, { argument := 1455179173366850679077125226496, coefficient := 1455179173366850679077125226496 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 2631995923212515302903105191936, coefficient := 2631995923212515302903105191936 }, { argument := 1455179173366850679077125226496, coefficient := 1455179173366850679077125226496 }, { argument := 831843061458224513927369195520, coefficient := 831843061458224513927369195520 }, { argument := 83735037969787675156848574464, coefficient := 83735037969787675156848574464 }, { argument := 79208819701150503526748651520, coefficient := 79208819701150503526748651520 }, { argument := 106366129312973533307348189184, coefficient := 106366129312973533307348189184 }, { argument := 61877194923640447660557825212416, coefficient := (-61877194923640447660557825212416) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11
