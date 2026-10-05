import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1879727927061485062194636448071680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6199634355, 301087965, 7348953, 1208304375, 189153273125, 47288335625,
    4833286875, 2569668100477737, 3675, 3045, 74133078763696899, 20475,
    20557305965736885, 82005, 82005, 58695, 3045, 144996525,
    22698392775, 5674600275, 579994425, 13362913633, 3885, 3219,
    49687290479, 21645, 835006339, 86691, 86691, 62049,
    3219, 6576391905185, 6576391790687, 110121, 82005, 86691,
    7029, 1506549, 2724909, 82005, 1506549, 44517,
    44517, 86691, 86691, 2724909, 86691, 110121,
    7029, 14311119, 586329195, 12072972165, 586329195, 14311119,
    110121, 82005, 86691, 7029, 1506549, 2724909,
    82005, 1506549, 44517, 44517
  ]
def negativeCoefficients : Array ℕ := #[
    228726136594524776980398735360, 22216370536116075588495605760, 135564255200720030477058048, 44578563137537147393802240000, 1744631010020678974371266560000, 1744631649892114031171338240000,
    44579203008972204193873920000, 5786378149888693313779349323776, 277675149192735138565324800, 14379605940338069675704320, 20866606618500811539193207455744, 386761814947023943001702400,
    5786367217939619356076471746560, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 2674713788252228843628134400,
    104677860601240738462275993600, 104677898993526841870280294400, 2674752180538332251632435200, 61625561966758831042940895232, 293542300575177146483343360, 15201297708357387942887424,
    229142182795544569555258966016, 408862490086853882601799680, 61612592941832635376830775296, 409386672766452413220519936, 409386672766452413220519936, 293018117895578615864623104,
    15201297708357387942887424, 14808718066816756130649210880, 14808717808990181063315685376, 520031719460088200577417216, 387257663427725255749140480, 409386672766452413220519936,
    531096224129451779313106944, 7114476502400781127048495104, 12868018930469842069607153664, 387257663427725255749140480, 7114476502400781127048495104, 420451177435815991956209664,
    420451177435815991956209664, 409386672766452413220519936, 409386672766452413220519936, 12868018930469842069607153664, 409386672766452413220519936, 520031719460088200577417216,
    531096224129451779313106944, 131996774800701082306609152, 21631729206218284125640458240, 222707027736774124954598768640, 21631729206218284125640458240, 131996774800701082306609152,
    520031719460088200577417216, 387257663427725255749140480, 409386672766452413220519936, 531096224129451779313106944, 7114476502400781127048495104, 12868018930469842069607153664,
    387257663427725255749140480, 7114476502400781127048495104, 420451177435815991956209664, 420451177435815991956209664
  ]
def negativeScales : Array ℕ := #[
    32, 28, 22, 30, 37, 35,
    32, 51, 11, 11, 56, 14,
    54, 16, 16, 15, 11, 27,
    34, 32, 29, 33, 11, 11,
    35, 14, 29, 16, 16, 15,
    11, 42, 42, 16, 16, 16,
    12, 20, 21, 16, 20, 15,
    15, 16, 16, 21, 16, 16,
    12, 23, 29, 33, 29, 23,
    16, 16, 16, 12, 20, 21,
    16, 20, 15, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32529535984037463, 28165609801330126, 22809107294974936, 30170336773045491, 37460764784887173, 35460765314018647,
    32170357481041801, 51190503455602566, 11843528536141147, 11572226512796267, 56040966946284472, 14321575831415734,
    54190500729979870, 16323424255808103, 16323424255808103, 15840949991965165, 11572226512796267, 27111443083991923,
    34401871095833543, 32401871624965016, 29111463791988233, 33637515554424517, 11923698889934521, 11652396861500322,
    35532157820625766, 14401746180099724, 29637211909047213, 16403594604492093, 16403594604492093, 15921120345540660,
    11652396861500322, 42580433414377364, 42580433389259381, 16748730090759493, 16323424255808103, 16403594604492093,
    12779103740003643, 20522816166191654, 21377776620336357, 16323424255808103, 20522816166191654, 15442068752306756,
    15442068752306756, 16403594604492093, 16403594604492093, 21377776620336357, 16403594604492093, 16748730090759493,
    12779103740003643, 23770633146734048, 29127135653515491, 33491061836222321, 29127135653515491, 23770633146734048,
    16748730090759493, 16323424255808103, 16403594604492093, 12779103740003643, 20522816166191654, 21377776620336357,
    16323424255808103, 20522816166191654, 15442068752306756, 15442068752306756
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
noncomputable def negativeCeiling : ℝ := 11724056601 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 228726136594524776980398735360, coefficient := (-228726136594524776980398735360) }, { argument := 22216370536116075588495605760, coefficient := (-22216370536116075588495605760) }, { argument := 135564255200720030477058048, coefficient := (-135564255200720030477058048) }, { argument := 44578563137537147393802240000, coefficient := (-44578563137537147393802240000) }, { argument := 1744631010020678974371266560000, coefficient := (-1744631010020678974371266560000) }, { argument := 1744631649892114031171338240000, coefficient := (-1744631649892114031171338240000) }, { argument := 44579203008972204193873920000, coefficient := (-44579203008972204193873920000) }, { argument := 5786378149888693313779349323776, coefficient := (-5786378149888693313779349323776) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 20866606618500811539193207455744, coefficient := (-20866606618500811539193207455744) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 5786367217939619356076471746560, coefficient := (-5786367217939619356076471746560) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 2674713788252228843628134400, coefficient := (-2674713788252228843628134400) }, { argument := 104677860601240738462275993600, coefficient := (-104677860601240738462275993600) }, { argument := 104677898993526841870280294400, coefficient := (-104677898993526841870280294400) }, { argument := 2674752180538332251632435200, coefficient := (-2674752180538332251632435200) }, { argument := 61625561966758831042940895232, coefficient := (-61625561966758831042940895232) }, { argument := 293542300575177146483343360, coefficient := (-293542300575177146483343360) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 229142182795544569555258966016, coefficient := (-229142182795544569555258966016) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 61612592941832635376830775296, coefficient := (-61612592941832635376830775296) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 14808718066816756130649210880, coefficient := (-14808718066816756130649210880) }, { argument := 14808717808990181063315685376, coefficient := (-14808717808990181063315685376) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 222707027736774124954598768640, coefficient := (-222707027736774124954598768640) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2491295395581355687436218009649152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    86691, 86691, 2724909, 86691, 110121, 7029,
    270364113, 11076867765, 228081284955, 11076867765, 270364113, 3818241825,
    597724343075, 149431140575, 15273186525, 14311119, 586329195, 12072972165,
    586329195, 14311119, 7588151475, 1187882555225, 296970747725, 30353041575,
    34462300747, 315, 261, 128141833637, 1755, 2153440513,
    7029, 7029, 5031, 261, 78819, 58695,
    62049, 5031, 1078311, 1950351, 58695, 1078311,
    31863, 31863, 62049, 62049, 1950351, 62049,
    78819, 5031, 165931623, 6798249315, 139981217805, 6798249315,
    165931623, 1208304375, 189153273125, 47288335625, 4833286875, 270364113,
    11076867765, 228081284955, 11076867765, 270364113
  ]
def negativeCoefficients : Array ℕ := #[
    409386672766452413220519936, 409386672766452413220519936, 12868018930469842069607153664, 409386672766452413220519936, 520031719460088200577417216, 531096224129451779313106944,
    4987337599226489542287556608, 817328579197112465071496232960, 8414714183135411532068353474560, 817328579197112465071496232960, 4987337599226489542287556608, 70434129757308692882207539200,
    2756516995832672779506601164800, 2756518006829540169250714419200, 70435140754176082626320793600, 131996774800701082306609152, 21631729206218284125640458240, 222707027736774124954598768640,
    21631729206218284125640458240, 131996774800701082306609152, 69988344125933321408269516800, 2739070685732465989762888499200, 2739071690330619028939001036800, 69989348724086360584382054400,
    79464655258889812964638982144, 380811633178608190032445440, 19720602432463638412394496, 295474951279700628579417063424, 530416203355918550402334720, 79447932042537613289918038016,
    531096224129451779313106944, 531096224129451779313106944, 380131612405074961121673216, 19720602432463638412394496, 372212203813302566098305024, 277179300712033825817886720,
    293018117895578615864623104, 380131612405074961121673216, 5092179724509650000025747456, 9210272192231295412177207296, 277179300712033825817886720, 5092179724509650000025747456,
    300937526487351010887991296, 300937526487351010887991296, 293018117895578615864623104, 293018117895578615864623104, 9210272192231295412177207296, 293018117895578615864623104,
    372212203813302566098305024, 380131612405074961121673216, 1530449091608128765122576384, 250811130526152537564858286080, 2582197699975029719068185722880, 250811130526152537564858286080,
    1530449091608128765122576384, 44578563137537147393802240000, 1744631010020678974371266560000, 1744631649892114031171338240000, 44579203008972204193873920000, 4987337599226489542287556608,
    817328579197112465071496232960, 8414714183135411532068353474560, 817328579197112465071496232960, 4987337599226489542287556608
  ]
def negativeScales : Array ℕ := #[
    16, 16, 21, 16, 16, 12,
    28, 33, 37, 33, 28, 31,
    39, 37, 33, 23, 29, 33,
    29, 23, 32, 40, 38, 34,
    35, 8, 8, 36, 10, 31,
    12, 12, 12, 8, 16, 15,
    15, 12, 20, 20, 15, 20,
    14, 14, 15, 15, 20, 15,
    16, 12, 27, 32, 37, 32,
    27, 30, 37, 35, 32, 28,
    33, 37, 33, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16403594604492093, 16403594604492093, 21377776620336357, 16403594604492093, 16748730090759493, 12779103740003643,
    28010328426129825, 33366830933261979, 37730757116115418, 33366830933261979, 28010328426129825, 31830261332630486,
    39120689343289482, 37120689872420956, 33830282040627275, 23770633146734048, 29127135653515491, 33491061836222321,
    29127135653515491, 23770633146734048, 32821101333149740, 40111529344004006, 38111529873135480, 34821122041146455,
    35004299969806341, 8299208018387279, 8027905996569885, 36898950587957878, 10777255315595305, 31003996324867978,
    12779103740003643, 12779103740003643, 12296629474285503, 8027905996569885, 16266255825241984, 15840949991965165,
    15921120345540660, 12296629474285503, 20040341900892294, 20895302359051428, 15840949991965165, 20040341900892294,
    14959594499254218, 14959594499254218, 15921120345540660, 15921120345540660, 20895302359051428, 15921120345540660,
    16266255825241984, 12296629474285503, 27306013618253934, 32662516125415289, 37026442308092716, 32662516125415289,
    27306013618253934, 30170336773045491, 37460764784887173, 35460765314018647, 32170357481041801, 28010328426129825,
    33366830933261979, 37730757116115418, 33366830933261979, 28010328426129825
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
noncomputable def negativeCeiling : ℝ := 8704879069 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 409386672766452413220519936, coefficient := (-409386672766452413220519936) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 4987337599226489542287556608, coefficient := (-4987337599226489542287556608) }, { argument := 817328579197112465071496232960, coefficient := (-817328579197112465071496232960) }, { argument := 8414714183135411532068353474560, coefficient := (-8414714183135411532068353474560) }, { argument := 817328579197112465071496232960, coefficient := (-817328579197112465071496232960) }, { argument := 4987337599226489542287556608, coefficient := (-4987337599226489542287556608) }, { argument := 70434129757308692882207539200, coefficient := (-70434129757308692882207539200) }, { argument := 2756516995832672779506601164800, coefficient := (-2756516995832672779506601164800) }, { argument := 2756518006829540169250714419200, coefficient := (-2756518006829540169250714419200) }, { argument := 70435140754176082626320793600, coefficient := (-70435140754176082626320793600) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 222707027736774124954598768640, coefficient := (-222707027736774124954598768640) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 69988344125933321408269516800, coefficient := (-69988344125933321408269516800) }, { argument := 2739070685732465989762888499200, coefficient := (-2739070685732465989762888499200) }, { argument := 2739071690330619028939001036800, coefficient := (-2739071690330619028939001036800) }, { argument := 69989348724086360584382054400, coefficient := (-69989348724086360584382054400) }, { argument := 79464655258889812964638982144, coefficient := (-79464655258889812964638982144) }, { argument := 380811633178608190032445440, coefficient := (-380811633178608190032445440) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 295474951279700628579417063424, coefficient := (-295474951279700628579417063424) }, { argument := 530416203355918550402334720, coefficient := (-530416203355918550402334720) }, { argument := 79447932042537613289918038016, coefficient := (-79447932042537613289918038016) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 531096224129451779313106944, coefficient := (-531096224129451779313106944) }, { argument := 380131612405074961121673216, coefficient := (-380131612405074961121673216) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 372212203813302566098305024, coefficient := (-372212203813302566098305024) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 380131612405074961121673216, coefficient := (-380131612405074961121673216) }, { argument := 5092179724509650000025747456, coefficient := (-5092179724509650000025747456) }, { argument := 9210272192231295412177207296, coefficient := (-9210272192231295412177207296) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 5092179724509650000025747456, coefficient := (-5092179724509650000025747456) }, { argument := 300937526487351010887991296, coefficient := (-300937526487351010887991296) }, { argument := 300937526487351010887991296, coefficient := (-300937526487351010887991296) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 9210272192231295412177207296, coefficient := (-9210272192231295412177207296) }, { argument := 293018117895578615864623104, coefficient := (-293018117895578615864623104) }, { argument := 372212203813302566098305024, coefficient := (-372212203813302566098305024) }, { argument := 380131612405074961121673216, coefficient := (-380131612405074961121673216) }, { argument := 1530449091608128765122576384, coefficient := (-1530449091608128765122576384) }, { argument := 250811130526152537564858286080, coefficient := (-250811130526152537564858286080) }, { argument := 2582197699975029719068185722880, coefficient := (-2582197699975029719068185722880) }, { argument := 250811130526152537564858286080, coefficient := (-250811130526152537564858286080) }, { argument := 1530449091608128765122576384, coefficient := (-1530449091608128765122576384) }, { argument := 44578563137537147393802240000, coefficient := (-44578563137537147393802240000) }, { argument := 1744631010020678974371266560000, coefficient := (-1744631010020678974371266560000) }, { argument := 1744631649892114031171338240000, coefficient := (-1744631649892114031171338240000) }, { argument := 44579203008972204193873920000, coefficient := (-44579203008972204193873920000) }, { argument := 4987337599226489542287556608, coefficient := (-4987337599226489542287556608) }, { argument := 817328579197112465071496232960, coefficient := (-817328579197112465071496232960) }, { argument := 8414714183135411532068353474560, coefficient := (-8414714183135411532068353474560) }, { argument := 817328579197112465071496232960, coefficient := (-817328579197112465071496232960) }, { argument := 4987337599226489542287556608, coefficient := (-4987337599226489542287556608) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
