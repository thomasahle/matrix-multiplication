import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

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
def constantNumerator : ℤ := (-26420710984641848839291103346688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28935, 14535, 1395, 16695, 1395, 324898329,
    15782011367, 33915, 30039, 1406019, 382755, 7891003797,
    1406019, 33915, 33915, 14535, 33915, 382755,
    14535, 162451051, 30039, 3833647, 248819317, 2623284135,
    248819381, 3833647, 4043729, 3833647, 4043729, 3833647,
    702237863671, 166216869, 3936341278985, 208473783, 7646345, 208366263,
    162451051, 703651221239, 166216869, 934227, 1407339714327, 113345537779945,
    3255, 2883, 134943, 36735, 56672787525897, 134943,
    3255, 3255, 1395, 3255, 36735, 1395,
    703651221239, 2883, 2883, 34503, 51615, 14973,
    2883, 59799, 30039, 2883
  ]
def negativeCoefficients : Array ℕ := #[
    273283348363666368516587520, 274558387314041172724285440, 13175402487206310146211840, 315359633726034907370618880, 13175402487206310146211840, 749164540629860768922206208,
    36390840581928003682523152384, 320318118533048034844999680, 283710333557842545148428288, 13279473999755791387431272448, 3615018766301542107536424960, 36390831881982329919255871488,
    13279473999755791387431272448, 320318118533048034844999680, 320318118533048034844999680, 274558387314041172724285440, 320318118533048034844999680, 3615018766301542107536424960,
    274558387314041172724285440, 749173240575534532189487104, 283710333557842545148428288, 141436610155888802848047104, 18359625045176833157877465088, 193564204283870149408865648640,
    18359629767543316027522678784, 141436610155888802848047104, 149187267932874902893232128, 141436610155888802848047104, 149187267932874902893232128, 141436610155888802848047104,
    395324772644271096281956352, 766540010794076721251352576, 4431926279309986909273456640, 961415630269765267155320832, 35262542328572165362810880, 960919781789063954407882752,
    749173240575534532189487104, 396120422221344355089645568, 766540010794076721251352576, 34466892751498906555121664, 396130913314173593176768512, 31903932606866798652864593920,
    15371302901740695170580480, 13614582570113187151085568, 637250300297878534071779328, 173476132748216416925122560, 31903943097959627890951716864, 637250300297878534071779328,
    15371302901740695170580480, 15371302901740695170580480, 13175402487206310146211840, 15371302901740695170580480, 173476132748216416925122560, 13175402487206310146211840,
    396120422221344355089645568, 13614582570113187151085568, 13614582570113187151085568, 325871621516902737616306176, 243744946013316737704919040, 282831973392028791138680832,
    13614582570113187151085568, 282392793309121914133807104, 283710333557842545148428288, 13614582570113187151085568
  ]
def negativeScales : Array ℕ := #[
    14, 13, 10, 14, 10, 28,
    33, 15, 14, 20, 18, 32,
    20, 15, 15, 13, 15, 18,
    13, 27, 14, 21, 27, 31,
    27, 21, 21, 21, 21, 21,
    39, 27, 41, 27, 22, 27,
    27, 39, 27, 19, 40, 46,
    11, 11, 17, 15, 45, 17,
    11, 11, 10, 11, 15, 10,
    39, 11, 11, 15, 15, 13,
    11, 15, 14, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14820528024633809, 13827243452138220, 10446049406716591, 14027128472950479, 10446049406716591, 28275413082792111,
    33877562035727704, 15049635872360048, 14874549168549452, 20423184659481843, 18546061698480726, 32877561690823039,
    20423184659481843, 15049635872360048, 15049635872360048, 13827243452138220, 15049635872360048, 18546061698480726,
    13827243452138220, 27275429836515653, 14874549168549452, 21870286072458942, 27890523255717960, 31288726932254375,
    27890523626800390, 21870286072458942, 21947254894158012, 21870286072458942, 21947254894158012, 21870286072458942,
    39353168830150097, 27308491564718929, 41839992447176116, 27635290725449872, 22866338867141613, 27634546465987359,
    27275429836515653, 39356069549222696, 27308491564718929, 19833413616618607, 40356107757924708, 46687720924236380,
    11668441828086828, 11493355121495124, 17041990615174776, 15164867654172497, 45687721398643260, 17041990615174776,
    11668441828086828, 11668441828086828, 10446049406716591, 11668441828086828, 15164867654172497, 10446049406716591,
    39356069549222696, 11493355121495124, 11493355121495124, 15074434187728835, 15655502772369993, 13870075691751301,
    11493355121495124, 15867833740861174, 14874549168549452, 11493355121495124
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
noncomputable def negativeCeiling : ℝ := 164390107 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 274558387314041172724285440, coefficient := (-274558387314041172724285440) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 749164540629860768922206208, coefficient := (-749164540629860768922206208) }, { argument := 36390840581928003682523152384, coefficient := (-36390840581928003682523152384) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 283710333557842545148428288, coefficient := (-283710333557842545148428288) }, { argument := 13279473999755791387431272448, coefficient := (-13279473999755791387431272448) }, { argument := 3615018766301542107536424960, coefficient := (-3615018766301542107536424960) }, { argument := 36390831881982329919255871488, coefficient := (-36390831881982329919255871488) }, { argument := 13279473999755791387431272448, coefficient := (-13279473999755791387431272448) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 274558387314041172724285440, coefficient := (-274558387314041172724285440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 3615018766301542107536424960, coefficient := (-3615018766301542107536424960) }, { argument := 274558387314041172724285440, coefficient := (-274558387314041172724285440) }, { argument := 749173240575534532189487104, coefficient := (-749173240575534532189487104) }, { argument := 283710333557842545148428288, coefficient := (-283710333557842545148428288) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 18359625045176833157877465088, coefficient := (-18359625045176833157877465088) }, { argument := 193564204283870149408865648640, coefficient := (-193564204283870149408865648640) }, { argument := 18359629767543316027522678784, coefficient := (-18359629767543316027522678784) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 395324772644271096281956352, coefficient := (-395324772644271096281956352) }, { argument := 766540010794076721251352576, coefficient := (-766540010794076721251352576) }, { argument := 4431926279309986909273456640, coefficient := (-4431926279309986909273456640) }, { argument := 961415630269765267155320832, coefficient := (-961415630269765267155320832) }, { argument := 35262542328572165362810880, coefficient := (-35262542328572165362810880) }, { argument := 960919781789063954407882752, coefficient := (-960919781789063954407882752) }, { argument := 749173240575534532189487104, coefficient := (-749173240575534532189487104) }, { argument := 396120422221344355089645568, coefficient := (-396120422221344355089645568) }, { argument := 766540010794076721251352576, coefficient := (-766540010794076721251352576) }, { argument := 34466892751498906555121664, coefficient := (-34466892751498906555121664) }, { argument := 396130913314173593176768512, coefficient := (-396130913314173593176768512) }, { argument := 31903932606866798652864593920, coefficient := (-31903932606866798652864593920) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 31903943097959627890951716864, coefficient := (-31903943097959627890951716864) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 396120422221344355089645568, coefficient := (-396120422221344355089645568) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 282831973392028791138680832, coefficient := (-282831973392028791138680832) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 283710333557842545148428288, coefficient := (-283710333557842545148428288) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }] }

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
def constantNumerator : ℤ := 574203916384352578636000138362880
def positiveArguments : Array ℕ := #[
    5, 9, 1, 1, 1, 1,
    93, 1113, 1665, 483, 93, 1929,
    969, 93
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 1426106925256758076683791106048, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672,
    3597763239173136423925579776, 86114203982789265372670328832, 64411567669067442428345057280, 74740629871854834097034625024, 3597763239173136423925579776, 74624572993171829696262832128,
    74972743629220842898578210816, 3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    2, 3, 0, 0, 0, 0,
    6, 10, 10, 8, 6, 10,
    9, 6
  ]
def negativeArguments : Array ℕ := #[
    34503, 2883, 332430231, 14700672105, 38955, 34503,
    1614963, 439635, 7350334299, 1614963, 38955, 38955,
    16695, 38955, 439635, 16695, 166216869, 34503,
    4043729, 264333323, 2784984025, 264333387, 4043729, 1868433,
    87902319, 3255, 2883, 134943, 36735, 43951149,
    134943, 3255, 3255, 1395, 3255, 36735,
    1395, 934227, 2883, 3833647, 248819317, 2623284135,
    248819381, 3833647, 253413, 9183771, 73470195, 2027277,
    9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    325871621516902737616306176, 13614582570113187151085568, 766531924202643408826662912, 33897442004057008664173608960, 367919572680374058599055360, 325871621516902737616306176,
    15252894284549221686492266496, 4152235177392792947046481920, 33897433917465575351748919296, 15252894284549221686492266496, 367919572680374058599055360, 367919572680374058599055360,
    315359633726034907370618880, 367919572680374058599055360, 4152235177392792947046481920, 315359633726034907370618880, 766540010794076721251352576, 325871621516902737616306176,
    149187267932874902893232128, 19504356638136810861989199872, 205495550234178094961891737600, 19504361360503293731634413568, 149187267932874902893232128, 34466505369873358654537728,
    1621511582078576519496597504, 15371302901740695170580480, 13614582570113187151085568, 637250300297878534071779328, 173476132748216416925122560, 1621511194696950971596013568,
    637250300297878534071779328, 15371302901740695170580480, 15371302901740695170580480, 13175402487206310146211840, 15371302901740695170580480, 173476132748216416925122560,
    13175402487206310146211840, 34466892751498906555121664, 13614582570113187151085568, 141436610155888802848047104, 18359625045176833157877465088, 193564204283870149408865648640,
    18359629767543316027522678784, 141436610155888802848047104, 9573672460187563220306755584, 346953058854001955950641020928, 346953186357896993431061790720, 9573544956292525739885985792,
    1426106925256758076683791106048, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    15, 11, 28, 33, 15, 15,
    20, 18, 32, 20, 15, 15,
    14, 15, 18, 14, 27, 15,
    21, 27, 31, 27, 21, 20,
    26, 11, 11, 17, 15, 25,
    17, 11, 11, 10, 11, 15,
    10, 19, 11, 21, 27, 31,
    27, 21, 17, 23, 26, 20,
    3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 3169925001442312, 0, 0, 0, 0,
    6539158811107971, 10120237877341959, 10701306461953989, 8915879378478017, 6539158811107971, 10913637427705176,
    9920352855028171, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15074434187728835, 11493355121495124, 28308476344969494, 33775163064891623, 15249520894286927, 15074434187728835,
    20623069681419278, 18745946720612189, 32775162720721498, 20623069681419278, 15249520894286927, 15249520894286927,
    14027128472950479, 15249520894286927, 18745946720612189, 14027128472950479, 27308491564718929, 15074434187728835,
    21947254894158012, 27977783084448744, 31375021906104757, 27977783433752022, 21947254894158012, 20833397401733542,
    26389397890623090, 11668441828086828, 11493355121495124, 17041990615174776, 15164867654172497, 25389397545960972,
    17041990615174776, 11668441828086828, 11668441828086828, 10446049406716591, 11668441828086828, 15164867654172497,
    10446049406716591, 19833413616618607, 11493355121495124, 21870286072458942, 27890523255717960, 31288726932254375,
    27890523626800390, 21870286072458942, 17951131021199719, 23130655237765982, 26130655767950681, 20951111806995793,
    3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 50
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
noncomputable def positiveFloor : ℝ := 277978411 / 1000000000000
noncomputable def negativeCeiling : ℝ := 479792929 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 766531924202643408826662912, coefficient := (-766531924202643408826662912) }, { argument := 33897442004057008664173608960, coefficient := (-33897442004057008664173608960) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 33897433917465575351748919296, coefficient := (-33897433917465575351748919296) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 766540010794076721251352576, coefficient := (-766540010794076721251352576) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 19504356638136810861989199872, coefficient := (-19504356638136810861989199872) }, { argument := 205495550234178094961891737600, coefficient := (-205495550234178094961891737600) }, { argument := 19504361360503293731634413568, coefficient := (-19504361360503293731634413568) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 34466505369873358654537728, coefficient := (-34466505369873358654537728) }, { argument := 1621511582078576519496597504, coefficient := (-1621511582078576519496597504) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 1621511194696950971596013568, coefficient := (-1621511194696950971596013568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 34466892751498906555121664, coefficient := (-34466892751498906555121664) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 18359625045176833157877465088, coefficient := (-18359625045176833157877465088) }, { argument := 193564204283870149408865648640, coefficient := (-193564204283870149408865648640) }, { argument := 18359629767543316027522678784, coefficient := (-18359629767543316027522678784) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 9573672460187563220306755584, coefficient := (-9573672460187563220306755584) }, { argument := 346953058854001955950641020928, coefficient := (-346953058854001955950641020928) }, { argument := 346953186357896993431061790720, coefficient := (-346953186357896993431061790720) }, { argument := 9573544956292525739885985792, coefficient := (-9573544956292525739885985792) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 74740629871854834097034625024, coefficient := 74740629871854834097034625024 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 74972743629220842898578210816, coefficient := 74972743629220842898578210816 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
