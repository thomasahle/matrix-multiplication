import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23641140468508502497997294141440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35187, 70263, 3441, 83361, 3441, 273671571,
    16075868781, 70263, 5697, 1221057, 2208537, 4018967673,
    1221057, 36081, 36081, 70263, 70263, 2208537,
    70263, 68417415, 5697, 9018645, 4125402175, 43282081575,
    2062704675, 9018645, 2257365, 9018645, 4496705, 9018645,
    28652770493, 10165389, 926397347051, 68132937, 3343629, 34048635,
    68417415, 3591575243, 10165389, 3343629, 3591587147, 472942688949,
    3441, 279, 59799, 108159, 472942700853, 59799,
    1767, 1767, 3441, 3441, 108159, 3441,
    3591575243, 279, 279, 6759, 5121, 2853,
    279, 2853, 5697, 279
  ]
def negativeCoefficients : Array ℕ := #[
    332331818865468412268642304, 331807636185869881649922048, 16249663067554449180327936, 393661192378496494658912256, 16249663067554449180327936, 631043678810879098557038592,
    37068429645705517960645312512, 331807636185869881649922048, 430453149646533900518817792, 5766278650473360375699996672, 10429521104977477631320522752, 37068434052171508568014454784,
    5766278650473360375699996672, 340775410136839337910730752, 340775410136839337910730752, 331807636185869881649922048, 331807636185869881649922048, 10429521104977477631320522752,
    331807636185869881649922048, 631039272344888491187896320, 430453149646533900518817792, 83182318103320139566940160, 19025059530837436138730291200, 199603370447861156475096268800,
    19025092619684618355238502400, 83182318103320139566940160, 83282068871898723967303680, 83182318103320139566940160, 82949566309970109299425280, 83182318103320139566940160,
    64520303257703571483787264, 750073317170809060768874496, 2086061373487949830735003648, 628415425914588118275588096, 30839534220216697180127232, 628086455904149618986844160,
    631039272344888491187896320, 64700067704191594488922112, 750073317170809060768874496, 30839534220216697180127232, 64700282147591451362459648, 8519778070873267186031394816,
    16249663067554449180327936, 21080643979530096233938944, 282392793309121914133807104, 510766436420697956668145664, 8519778285316667042904932352, 282392793309121914133807104,
    16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936, 16249663067554449180327936, 510766436420697956668145664, 16249663067554449180327936,
    64700067704191594488922112, 21080643979530096233938944, 21080643979530096233938944, 510695600923454911989940224, 386931820140407250229395456, 431133170420067129429590016,
    21080643979530096233938944, 431133170420067129429590016, 430453149646533900518817792, 21080643979530096233938944
  ]
def negativeScales : Array ℕ := #[
    15, 16, 11, 16, 11, 28,
    33, 16, 12, 20, 21, 31,
    20, 15, 15, 16, 16, 21,
    16, 26, 12, 23, 31, 35,
    30, 23, 21, 23, 22, 23,
    34, 23, 39, 26, 21, 25,
    26, 31, 23, 21, 31, 38,
    11, 8, 15, 16, 38, 15,
    10, 10, 11, 11, 16, 11,
    31, 8, 8, 12, 12, 11,
    8, 11, 12, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15102754896489514, 16100477555778448, 11748612176955137, 16347084963864379, 11748612176955137, 28027870334439218,
    33904177660164140, 16100477555778448, 12475986690870773, 20219699117477445, 21074659571622716, 31904177831662820,
    20219699117477445, 15138951703593084, 15138951703593084, 16100477555778448, 16100477555778448, 21074659571622716,
    16100477555778448, 26027860260320671, 12475986690870773, 23104479262380694, 31941887633966610, 35333050833567806,
    30941890143135191, 23104479262380694, 21106208280328534, 23104479262380694, 22100436810458735, 23104479262380694,
    34737955591807230, 23277162088211975, 39752840165848710, 26021849062435113, 21672983348134433, 25021093626378276,
    26027860260320671, 31741969594272720, 23277162088211975, 21672983348134433, 31741974375966605, 38782874413025574,
    11748612176955137, 8124121311829188, 15867833740861174, 16722794192703879, 38782874449338307, 15867833740861174,
    10787086325046961, 10787086325046961, 11748612176955137, 11748612176955137, 16722794192703879, 11748612176955137,
    31741969594272720, 8124121311829188, 8124121311829188, 12722594099078657, 12322209843748895, 11478264031581849,
    8124121311829188, 11478264031581849, 12475986690870773, 8124121311829188
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
noncomputable def negativeCeiling : ℝ := 74374803 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 631043678810879098557038592, coefficient := (-631043678810879098557038592) }, { argument := 37068429645705517960645312512, coefficient := (-37068429645705517960645312512) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 430453149646533900518817792, coefficient := (-430453149646533900518817792) }, { argument := 5766278650473360375699996672, coefficient := (-5766278650473360375699996672) }, { argument := 10429521104977477631320522752, coefficient := (-10429521104977477631320522752) }, { argument := 37068434052171508568014454784, coefficient := (-37068434052171508568014454784) }, { argument := 5766278650473360375699996672, coefficient := (-5766278650473360375699996672) }, { argument := 340775410136839337910730752, coefficient := (-340775410136839337910730752) }, { argument := 340775410136839337910730752, coefficient := (-340775410136839337910730752) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 10429521104977477631320522752, coefficient := (-10429521104977477631320522752) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 631039272344888491187896320, coefficient := (-631039272344888491187896320) }, { argument := 430453149646533900518817792, coefficient := (-430453149646533900518817792) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 19025059530837436138730291200, coefficient := (-19025059530837436138730291200) }, { argument := 199603370447861156475096268800, coefficient := (-199603370447861156475096268800) }, { argument := 19025092619684618355238502400, coefficient := (-19025092619684618355238502400) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 83282068871898723967303680, coefficient := (-83282068871898723967303680) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 82949566309970109299425280, coefficient := (-82949566309970109299425280) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 64520303257703571483787264, coefficient := (-64520303257703571483787264) }, { argument := 750073317170809060768874496, coefficient := (-750073317170809060768874496) }, { argument := 2086061373487949830735003648, coefficient := (-2086061373487949830735003648) }, { argument := 628415425914588118275588096, coefficient := (-628415425914588118275588096) }, { argument := 30839534220216697180127232, coefficient := (-30839534220216697180127232) }, { argument := 628086455904149618986844160, coefficient := (-628086455904149618986844160) }, { argument := 631039272344888491187896320, coefficient := (-631039272344888491187896320) }, { argument := 64700067704191594488922112, coefficient := (-64700067704191594488922112) }, { argument := 750073317170809060768874496, coefficient := (-750073317170809060768874496) }, { argument := 30839534220216697180127232, coefficient := (-30839534220216697180127232) }, { argument := 64700282147591451362459648, coefficient := (-64700282147591451362459648) }, { argument := 8519778070873267186031394816, coefficient := (-8519778070873267186031394816) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 8519778285316667042904932352, coefficient := (-8519778285316667042904932352) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 64700067704191594488922112, coefficient := (-64700067704191594488922112) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 386931820140407250229395456, coefficient := (-386931820140407250229395456) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 430453149646533900518817792, coefficient := (-430453149646533900518817792) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 539040242412116817084244939505664
def positiveArguments : Array ℕ := #[
    19, 141, 105, 111, 9, 1929,
    3489, 105, 1929, 57, 57, 111,
    111, 3489, 111, 141
  ]
def positiveCoefficients : Array ℕ := #[
    6021340351084089657109340225536, 5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128,
    134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152,
    4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112
  ]
def positiveScales : Array ℕ := #[
    4, 7, 6, 6, 3, 10,
    11, 6, 10, 5, 5, 6,
    6, 11, 6, 7
  ]
def negativeArguments : Array ℕ := #[
    6759, 279, 40661841, 2397386415, 83361, 6759,
    1448679, 2620239, 599346675, 1448679, 42807, 42807,
    83361, 83361, 2620239, 83361, 10165389, 6759,
    4496705, 2054572355, 21554588299, 1027287959, 4496705, 13374609,
    782383983, 3441, 279, 59799, 108159, 195596019,
    59799, 1767, 1767, 3441, 3441, 108159,
    3441, 3343629, 279, 9018645, 4125402175, 43282081575,
    2062704675, 9018645, 470259, 73616409, 18404109, 1881063
  ]
def negativeCoefficients : Array ℕ := #[
    510695600923454911989940224, 21080643979530096233938944, 750078574492870067991085056, 44223973643293037699939696640, 393661192378496494658912256, 510695600923454911989940224,
    6841193154037114758531907584, 12373728830707876305089593344, 44223978900615098707161907200, 6841193154037114758531907584, 404300684064401805325369344, 404300684064401805325369344,
    393661192378496494658912256, 393661192378496494658912256, 12373728830707876305089593344, 393661192378496494658912256, 750073317170809060768874496, 510695600923454911989940224,
    82949566309970109299425280, 18950085206801863524839587840, 198805986982913747393385070592, 18950118069676430838405791744, 82949566309970109299425280, 30839748663616554053664768,
    1804054637721315572308770816, 16249663067554449180327936, 21080643979530096233938944, 282392793309121914133807104, 510766436420697956668145664, 1804054852164715429182308352,
    282392793309121914133807104, 16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936, 16249663067554449180327936, 510766436420697956668145664,
    16249663067554449180327936, 30839534220216697180127232, 21080643979530096233938944, 83182318103320139566940160, 19025059530837436138730291200, 199603370447861156475096268800,
    19025092619684618355238502400, 83182318103320139566940160, 8882941359471185954189869056, 347643662450823295736337137664, 347643789954718333216757907456, 8883068863366223434610638848
  ]
def negativeScales : Array ℕ := #[
    12, 8, 25, 31, 16, 12,
    20, 21, 29, 20, 15, 15,
    16, 16, 21, 16, 23, 12,
    22, 30, 34, 29, 22, 23,
    29, 11, 8, 15, 16, 27,
    15, 10, 10, 11, 11, 16,
    11, 21, 8, 23, 31, 35,
    30, 23, 18, 26, 24, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4247927513443585, 7139551352398793, 6714245517659862, 6794415866314396, 3169925001442312, 10913637427705176,
    11768597882173550, 6714245517659862, 10913637427705176, 5832890014087662, 5832890014087662, 6794415866314396,
    6794415866314396, 11768597882173550, 6794415866314396, 7139551352398793
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12722594099078657, 8124121311829188, 25277172200137984, 31158815317864456, 16347084963864379, 12722594099078657,
    20466306525563460, 21321266979708647, 29158815489371252, 20466306525563460, 15385559111679018, 15385559111679018,
    16347084963864379, 16347084963864379, 21321266979708647, 16347084963864379, 23277162088211975, 12722594099078657,
    22100436810458735, 30936191000403848, 34327275955618125, 29936193502296121, 22100436810458735, 23672993379912215,
    29543301594774845, 11748612176955137, 8124121311829188, 15867833740861174, 16722794192703879, 27543301766264336,
    15867833740861174, 10787086325046961, 10787086325046961, 11748612176955137, 11748612176955137, 16722794192703879,
    11748612176955137, 21672983348134433, 8124121311829188, 23104479262380694, 31941887633966610, 35333050833567806,
    30941890143135191, 23104479262380694, 18843096030826774, 26133524041151017, 24133524570282491, 20843116738823689
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 92391151 / 250000000000
noncomputable def negativeCeiling : ℝ := 90911981 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 750078574492870067991085056, coefficient := (-750078574492870067991085056) }, { argument := 44223973643293037699939696640, coefficient := (-44223973643293037699939696640) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 44223978900615098707161907200, coefficient := (-44223978900615098707161907200) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 750073317170809060768874496, coefficient := (-750073317170809060768874496) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 82949566309970109299425280, coefficient := (-82949566309970109299425280) }, { argument := 18950085206801863524839587840, coefficient := (-18950085206801863524839587840) }, { argument := 198805986982913747393385070592, coefficient := (-198805986982913747393385070592) }, { argument := 18950118069676430838405791744, coefficient := (-18950118069676430838405791744) }, { argument := 82949566309970109299425280, coefficient := (-82949566309970109299425280) }, { argument := 30839748663616554053664768, coefficient := (-30839748663616554053664768) }, { argument := 1804054637721315572308770816, coefficient := (-1804054637721315572308770816) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 1804054852164715429182308352, coefficient := (-1804054852164715429182308352) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 30839534220216697180127232, coefficient := (-30839534220216697180127232) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 19025059530837436138730291200, coefficient := (-19025059530837436138730291200) }, { argument := 199603370447861156475096268800, coefficient := (-199603370447861156475096268800) }, { argument := 19025092619684618355238502400, coefficient := (-19025092619684618355238502400) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 8882941359471185954189869056, coefficient := (-8882941359471185954189869056) }, { argument := 347643662450823295736337137664, coefficient := (-347643662450823295736337137664) }, { argument := 347643789954718333216757907456, coefficient := (-347643789954718333216757907456) }, { argument := 8883068863366223434610638848, coefficient := (-8883068863366223434610638848) }, { argument := 6021340351084089657109340225536, coefficient := 6021340351084089657109340225536 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
