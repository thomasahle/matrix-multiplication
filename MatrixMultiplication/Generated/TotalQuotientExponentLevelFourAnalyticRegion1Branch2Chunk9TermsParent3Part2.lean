import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

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
def constantNumerator : ℤ := (-516569388495225935973359525298176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    274239, 74655, 1701, 274239, 6615, 6615,
    2835, 6615, 74655, 2835, 6615, 5859,
    2476215, 636741, 2476215, 2193219, 102656799, 27945855,
    636741, 102656799, 2476215, 2476215, 1061235, 2476215,
    27945855, 1061235, 2476215, 2193219, 3598030505, 215025096123,
    4093271, 1986327511737, 134943, 314867, 4093271, 4093271,
    134943, 50513663, 2024145, 107512618269, 4093271, 314867,
    2024145, 314867, 4093271, 4093271, 3966514857, 99225,
    25515, 99225, 87885, 4113585, 1119825, 25515,
    4113585, 99225, 99225, 42525, 99225, 1119825,
    42525, 99225, 87885, 139040701
  ]
def negativeCoefficients : Array ℕ := #[
    41441825980662036280280875008, 11281544632916267629711196160, 1028191409582242113087602688, 41441825980662036280280875008, 999630537093846498835169280, 999630537093846498835169280,
    856826174651868427573002240, 999630537093846498835169280, 11281544632916267629711196160, 856826174651868427573002240, 999630537093846498835169280, 885387047140264041825435648,
    23387189440758117045664481280, 24055394853351206104112037888, 23387189440758117045664481280, 20714367790385760811874254848, 969566053672572223807404638208, 263941137974270178086784860160,
    24055394853351206104112037888, 969566053672572223807404638208, 23387189440758117045664481280, 23387189440758117045664481280, 20046162377792671753426698240, 23387189440758117045664481280,
    263941137974270178086784860160, 20046162377792671753426698240, 23387189440758117045664481280, 20714367790385760811874254848, 4148246743445933451515002880, 247907057350361058338351874048,
    77319703102809262134042558464, 2290079703473796536291202957312, 40784019219064226180593876992, 2973834734723433159001636864, 77319703102809262134042558464, 77319703102809262134042558464,
    40784019219064226180593876992, 954176116312690125016810913792, 76470036035745424088613519360, 247907219237834127708770009088, 77319703102809262134042558464, 2973834734723433159001636864,
    76470036035745424088613519360, 2973834734723433159001636864, 77319703102809262134042558464, 77319703102809262134042558464, 4573080276977852474229522432, 1874307257050962185315942400,
    1927858892966703962039255040, 1874307257050962185315942400, 1660100713387995078422691840, 77703423713741318025526640640, 21152896186718001805708492800, 1927858892966703962039255040,
    77703423713741318025526640640, 1874307257050962185315942400, 1874307257050962185315942400, 1606549077472253301699379200, 1874307257050962185315942400, 21152896186718001805708492800,
    1606549077472253301699379200, 1874307257050962185315942400, 1660100713387995078422691840, 5129696454352343454168645632
  ]
def negativeScales : Array ℕ := #[
    18, 16, 10, 18, 12, 12,
    11, 12, 16, 11, 12, 12,
    21, 19, 21, 21, 26, 24,
    19, 26, 21, 21, 20, 21,
    24, 20, 21, 21, 31, 37,
    21, 40, 17, 18, 21, 21,
    17, 25, 20, 36, 21, 18,
    20, 18, 21, 21, 31, 16,
    14, 16, 16, 21, 20, 14,
    21, 16, 16, 15, 16, 20,
    15, 16, 16, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18065074228287818, 16187951267285539, 10732167425814919, 18065074228287818, 12691525441225267, 12691525441225267,
    11469133019829685, 12691525441225267, 16187951267285539, 11469133019829685, 12691525441225267, 12516438734608414,
    21239705152845485, 19280347137342831, 21239705152845485, 21064618446287393, 26613253939975389, 24736130979130559,
    19280347137342831, 26613253939975389, 21239705152845485, 21239705152845485, 20017312731509037, 21239705152845485,
    24736130979130559, 20017312731509037, 21239705152845485, 21064618446287393, 31744560272355466, 37645714094010008,
    21964822768012238, 40853240658927583, 17041990615174776, 18264383036511224, 21964822768012238, 21964822768012238,
    17041990615174776, 25590170326858519, 20948881221012139, 36645715036113798, 21964822768012238, 18264383036511224,
    20948881221012139, 18264383036511224, 21964822768012238, 21964822768012238, 31885224810093250, 16598416036779970,
    14639058021287992, 16598416036779970, 16423329330216484, 21971964838930244, 20094841862894057, 14639058021287992,
    21971964838930244, 16598416036779970, 16598416036779970, 15376023615438113, 16598416036779970, 20094841862894057,
    15376023615438113, 16598416036779970, 16423329330216484, 27050932020002186
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
noncomputable def negativeCeiling : ℝ := 2751306747 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 41441825980662036280280875008, coefficient := (-41441825980662036280280875008) }, { argument := 11281544632916267629711196160, coefficient := (-11281544632916267629711196160) }, { argument := 1028191409582242113087602688, coefficient := (-1028191409582242113087602688) }, { argument := 41441825980662036280280875008, coefficient := (-41441825980662036280280875008) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 856826174651868427573002240, coefficient := (-856826174651868427573002240) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 11281544632916267629711196160, coefficient := (-11281544632916267629711196160) }, { argument := 856826174651868427573002240, coefficient := (-856826174651868427573002240) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 885387047140264041825435648, coefficient := (-885387047140264041825435648) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 24055394853351206104112037888, coefficient := (-24055394853351206104112037888) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 20714367790385760811874254848, coefficient := (-20714367790385760811874254848) }, { argument := 969566053672572223807404638208, coefficient := (-969566053672572223807404638208) }, { argument := 263941137974270178086784860160, coefficient := (-263941137974270178086784860160) }, { argument := 24055394853351206104112037888, coefficient := (-24055394853351206104112037888) }, { argument := 969566053672572223807404638208, coefficient := (-969566053672572223807404638208) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 20046162377792671753426698240, coefficient := (-20046162377792671753426698240) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 263941137974270178086784860160, coefficient := (-263941137974270178086784860160) }, { argument := 20046162377792671753426698240, coefficient := (-20046162377792671753426698240) }, { argument := 23387189440758117045664481280, coefficient := (-23387189440758117045664481280) }, { argument := 20714367790385760811874254848, coefficient := (-20714367790385760811874254848) }, { argument := 4148246743445933451515002880, coefficient := (-4148246743445933451515002880) }, { argument := 247907057350361058338351874048, coefficient := (-247907057350361058338351874048) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 2290079703473796536291202957312, coefficient := (-2290079703473796536291202957312) }, { argument := 40784019219064226180593876992, coefficient := (-40784019219064226180593876992) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 40784019219064226180593876992, coefficient := (-40784019219064226180593876992) }, { argument := 954176116312690125016810913792, coefficient := (-954176116312690125016810913792) }, { argument := 76470036035745424088613519360, coefficient := (-76470036035745424088613519360) }, { argument := 247907219237834127708770009088, coefficient := (-247907219237834127708770009088) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 76470036035745424088613519360, coefficient := (-76470036035745424088613519360) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 4573080276977852474229522432, coefficient := (-4573080276977852474229522432) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1927858892966703962039255040, coefficient := (-1927858892966703962039255040) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1660100713387995078422691840, coefficient := (-1660100713387995078422691840) }, { argument := 77703423713741318025526640640, coefficient := (-77703423713741318025526640640) }, { argument := 21152896186718001805708492800, coefficient := (-21152896186718001805708492800) }, { argument := 1927858892966703962039255040, coefficient := (-1927858892966703962039255040) }, { argument := 77703423713741318025526640640, coefficient := (-77703423713741318025526640640) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1606549077472253301699379200, coefficient := (-1606549077472253301699379200) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 21152896186718001805708492800, coefficient := (-21152896186718001805708492800) }, { argument := 1606549077472253301699379200, coefficient := (-1606549077472253301699379200) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1660100713387995078422691840, coefficient := (-1660100713387995078422691840) }, { argument := 5129696454352343454168645632, coefficient := (-5129696454352343454168645632) }] }

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
def constantNumerator : ℤ := (-3712213527141191471371076014964736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13198134519, 1114295, 139443218445, 36735, 85715, 1114295,
    1114295, 36735, 13751135, 551025, 6599072193, 1114295,
    85715, 551025, 85715, 1114295, 1114295, 142175421,
    460812705, 16769125983, 67076519499, 1843235253, 16552170035325, 1912721227,
    88538859027331, 7916239031, 667188603, 15816485099, 3506745907, 16566211676285,
    1912721227, 660332333, 30759988942943, 1899243664861089, 896235725, 8314880903,
    109944915171, 6754573119, 949621839339721, 109944915171, 896235725, 7000121919,
    6945931839, 7000121919, 6754573119, 6945931839, 15379987562295, 8314880903,
    779974220651, 948253936988429, 25389, 38831751317983077, 837, 1953,
    25389, 25389, 837, 313317, 12555, 948253939255309,
    25389, 1953, 12555, 1953
  ]
def negativeCoefficients : Array ℕ := #[
    486925219444769427126283665408, 21048437440116925253581537280, 5144546726938580374945781514240, 11102472495885850683207843840, 809555286158343278983905280, 21048437440116925253581537280,
    21048437440116925253581537280, 11102472495885850683207843840, 259751596101662714942550179840, 20817135929785970031014707200, 486925583472816977710575255552, 21048437440116925253581537280,
    809555286158343278983905280, 20817135929785970031014707200, 809555286158343278983905280, 21048437440116925253581537280, 21048437440116925253581537280, 5245347209517821065452060672,
    17000988070097635729012162560, 618671550696388218398290477056, 618671694276620716116585480192, 17000844489865138010717159424, 9318043350407844951647846400, 17641739479410356004287676416,
    99685893130824191879931756544, 18253604428895936682511040512, 769216088027300298152214528, 18235165797930855049277210624, 16172011069489369109053308928, 9325948091532235738363985920,
    17641739479410356004287676416, 761311346902909511436075008, 69265337370679335972832804864, 4276716530677087804035088515072, 16532631048790533431990681600, 19172810002626996887571398656,
    253515714045642952964195745792, 498399526613404367835906441216, 4276716561793252514872076271616, 253515714045642952964195745792, 16532631048790533431990681600, 16141182190569697988352933888,
    16016228373432967175998537728, 16141182190569697988352933888, 498399526613404367835906441216, 16016228373432967175998537728, 69265306254514625135845048320, 19172810002626996887571398656,
    28101532875859493008250503168, 4270556077273694638354447990784, 1918338602137238757288443904, 43720665191453088126454934274048, 1011870911017444619229069312, 73782253928355336818786304,
    1918338602137238757288443904, 1918338602137238757288443904, 1011870911017444619229069312, 23673563189012298070713434112, 1897257958157708661054504960, 4270556087482814561648077963264,
    1918338602137238757288443904, 73782253928355336818786304, 1897257958157708661054504960, 73782253928355336818786304
  ]
def negativeScales : Array ℕ := #[
    33, 20, 37, 15, 16, 20,
    20, 15, 23, 19, 32, 20,
    16, 19, 16, 20, 20, 27,
    28, 33, 35, 30, 43, 30,
    46, 32, 29, 33, 31, 43,
    30, 29, 44, 50, 29, 32,
    36, 32, 49, 36, 29, 32,
    32, 32, 32, 32, 43, 32,
    39, 49, 14, 55, 9, 10,
    14, 14, 9, 18, 13, 49,
    14, 10, 13, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33619614976165481, 20087699793650037, 37020886817111289, 15164867654172497, 16387260075508949, 20087699793650037,
    20087699793650037, 15164867654172497, 23713047365950039, 19071758249781016, 32619616054732049, 20087699793650037,
    16387260075508949, 19071758249781016, 16387260075508949, 20087699793650037, 20087699793650037, 27083096835403906,
    28779605253186184, 33965088459015265, 35965088793833491, 30779593068990472, 43912085609698163, 30832979476051912,
    46331376015530135, 32882168032397063, 29313519403793023, 33880709976941910, 31707485753157226, 43913308967115018,
    30832979476051912, 29298617047964440, 44806120218972549, 50754346432539325, 29739302994418074, 32953048464385682,
    36677989926512154, 32653217449827976, 49754346443035961, 36677989926512154, 29739302994418074, 32704732903325454,
    32693521107552830, 32704732903325454, 32653217449827976, 32693521107552830, 43806119570868476, 32953048464385682,
    39504635485231605, 49752266785014768, 14631915952041241, 55108086292680679, 9709083812639846, 10931476241484805,
    14631915952041241, 14631915952041241, 9709083812639846, 18257263524229789, 13615974408167608, 49752266788463651,
    14631915952041241, 10931476241484805, 13615974408167608, 10931476241484805
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
noncomputable def negativeCeiling : ℝ := 2717973347 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 486925219444769427126283665408, coefficient := (-486925219444769427126283665408) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 5144546726938580374945781514240, coefficient := (-5144546726938580374945781514240) }, { argument := 11102472495885850683207843840, coefficient := (-11102472495885850683207843840) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 11102472495885850683207843840, coefficient := (-11102472495885850683207843840) }, { argument := 259751596101662714942550179840, coefficient := (-259751596101662714942550179840) }, { argument := 20817135929785970031014707200, coefficient := (-20817135929785970031014707200) }, { argument := 486925583472816977710575255552, coefficient := (-486925583472816977710575255552) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 20817135929785970031014707200, coefficient := (-20817135929785970031014707200) }, { argument := 809555286158343278983905280, coefficient := (-809555286158343278983905280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 21048437440116925253581537280, coefficient := (-21048437440116925253581537280) }, { argument := 5245347209517821065452060672, coefficient := (-5245347209517821065452060672) }, { argument := 17000988070097635729012162560, coefficient := (-17000988070097635729012162560) }, { argument := 618671550696388218398290477056, coefficient := (-618671550696388218398290477056) }, { argument := 618671694276620716116585480192, coefficient := (-618671694276620716116585480192) }, { argument := 17000844489865138010717159424, coefficient := (-17000844489865138010717159424) }, { argument := 9318043350407844951647846400, coefficient := (-9318043350407844951647846400) }, { argument := 17641739479410356004287676416, coefficient := (-17641739479410356004287676416) }, { argument := 99685893130824191879931756544, coefficient := (-99685893130824191879931756544) }, { argument := 18253604428895936682511040512, coefficient := (-18253604428895936682511040512) }, { argument := 769216088027300298152214528, coefficient := (-769216088027300298152214528) }, { argument := 18235165797930855049277210624, coefficient := (-18235165797930855049277210624) }, { argument := 16172011069489369109053308928, coefficient := (-16172011069489369109053308928) }, { argument := 9325948091532235738363985920, coefficient := (-9325948091532235738363985920) }, { argument := 17641739479410356004287676416, coefficient := (-17641739479410356004287676416) }, { argument := 761311346902909511436075008, coefficient := (-761311346902909511436075008) }, { argument := 69265337370679335972832804864, coefficient := (-69265337370679335972832804864) }, { argument := 4276716530677087804035088515072, coefficient := (-4276716530677087804035088515072) }, { argument := 16532631048790533431990681600, coefficient := (-16532631048790533431990681600) }, { argument := 19172810002626996887571398656, coefficient := (-19172810002626996887571398656) }, { argument := 253515714045642952964195745792, coefficient := (-253515714045642952964195745792) }, { argument := 498399526613404367835906441216, coefficient := (-498399526613404367835906441216) }, { argument := 4276716561793252514872076271616, coefficient := (-4276716561793252514872076271616) }, { argument := 253515714045642952964195745792, coefficient := (-253515714045642952964195745792) }, { argument := 16532631048790533431990681600, coefficient := (-16532631048790533431990681600) }, { argument := 16141182190569697988352933888, coefficient := (-16141182190569697988352933888) }, { argument := 16016228373432967175998537728, coefficient := (-16016228373432967175998537728) }, { argument := 16141182190569697988352933888, coefficient := (-16141182190569697988352933888) }, { argument := 498399526613404367835906441216, coefficient := (-498399526613404367835906441216) }, { argument := 16016228373432967175998537728, coefficient := (-16016228373432967175998537728) }, { argument := 69265306254514625135845048320, coefficient := (-69265306254514625135845048320) }, { argument := 19172810002626996887571398656, coefficient := (-19172810002626996887571398656) }, { argument := 28101532875859493008250503168, coefficient := (-28101532875859493008250503168) }, { argument := 4270556077273694638354447990784, coefficient := (-4270556077273694638354447990784) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 43720665191453088126454934274048, coefficient := (-43720665191453088126454934274048) }, { argument := 1011870911017444619229069312, coefficient := (-1011870911017444619229069312) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1011870911017444619229069312, coefficient := (-1011870911017444619229069312) }, { argument := 23673563189012298070713434112, coefficient := (-23673563189012298070713434112) }, { argument := 1897257958157708661054504960, coefficient := (-1897257958157708661054504960) }, { argument := 4270556087482814561648077963264, coefficient := (-4270556087482814561648077963264) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 1897257958157708661054504960, coefficient := (-1897257958157708661054504960) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
