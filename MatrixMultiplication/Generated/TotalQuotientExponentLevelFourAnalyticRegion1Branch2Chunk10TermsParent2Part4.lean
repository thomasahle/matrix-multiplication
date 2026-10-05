import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-786325463029057021596900719067136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    118128627735, 118128127977, 10344798171, 1995, 651, 18835677221,
    6573, 10344798171, 13167, 5901, 1995, 651,
    101393350785, 101392859007, 175, 38331179, 1415519445, 11324152787,
    306652205, 159303492243, 25935, 8463, 290003678573, 85449,
    159303492243, 171171, 76713, 25935, 8463, 118128627735,
    118128127977, 180022420041, 25935, 8463, 327976390071, 85449,
    180022420041, 171171, 76713, 25935, 8463, 676750464885,
    676743047307, 5649, 101393350785, 101392859007, 3773, 61523333461855,
    855, 279, 1705679978479701, 2817, 492186664338611, 5643,
    2529, 855, 279, 229309449593, 229308881543, 5052449,
    104941778295, 104941193865, 3507, 21
  ]
def negativeCoefficients : Array ℕ := #[
    136193035225378313960014479360, 136192459043633014651383447552, 23853480544326957342803361792, 150737938133199075221176320, 6148521160696278068232192, 86864229287696936585903734784,
    124160459567608711958495232, 23853480544326957342803361792, 124358798959889237057470464, 111466738461655105624080384, 150737938133199075221176320, 6148521160696278068232192,
    116898574544172028950384476160, 116898007562740336404392312832, 3384992294920961689177292800, 2828341796226200068010541056, 104446899733097534378716692480, 104446874156686876180423376896,
    2828367372636858266303856640, 734657687863698944023616028672, 3919186391463175955750584320, 159861550178103229774036992, 2674811819535228713303208361984, 3228171948757826510920876032,
    734657687863698944023616028672, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320, 159861550178103229774036992, 136193035225378313960014479360,
    136192459043633014651383447552, 415103438753271045756165292032, 3919186391463175955750584320, 159861550178103229774036992, 1512524132464717869191931101184, 3228171948757826510920876032,
    415103438753271045756165292032, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320, 159861550178103229774036992, 1560480328437194720324112875520,
    1560463224666818123030555787264, 109267551280048643326643011584, 116898574544172028950384476160, 116898007562740336404392312832, 72980433878495934018662432768, 138538230826700472841184215040,
    129203946971313493046722560, 5270160994882524058484736, 480106232218406066248646393856, 106423251057950324535853056, 138538229882005993230555938816, 106593256251333631763546112,
    95542918681418661963497472, 129203946971313493046722560, 5270160994882524058484736, 264375795645329493925736480768, 264375140728268802006311763968, 23859515814008256090293141504,
    120989632927989556494383185920, 120988959126074619114805002240, 67835245590216072251112947712, 3249592603124123221610201088
  ]
def negativeScales : Array ℕ := #[
    36, 36, 33, 10, 9, 34,
    12, 33, 13, 12, 10, 9,
    36, 36, 7, 25, 30, 33,
    28, 37, 14, 13, 38, 16,
    37, 17, 16, 14, 13, 36,
    36, 37, 14, 13, 38, 16,
    37, 17, 16, 14, 13, 39,
    39, 12, 36, 36, 11, 45,
    9, 8, 50, 11, 48, 12,
    11, 9, 8, 37, 37, 22,
    36, 36, 11, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36781567679440420, 36781561575924838, 33268186447088670, 10962173043893966, 9346513733165637, 34132748853983408,
    12682336269758884, 33268186447088670, 13684639055631019, 12526743743000334, 10962173043893966, 9346513733165637,
    36561172089555387, 36561165092179356, 7451211111832378, 25192015037807678, 30398684421677392, 33398684068397731,
    28192028083894976, 37212986937657688, 14662612749280074, 13046953451306728, 38077280244088664, 16382775987852475,
    37212986937657688, 17385078773721895, 16227183461140779, 14662612749280074, 13046953451306728, 36781567679440420,
    36781561575924838, 37389385635136710, 14662612749280074, 13046953451306728, 38254801007526733, 16382775987852475,
    37389385635136710, 17385078773721895, 16227183461140779, 14662612749280074, 13046953451306728, 39299833017242310,
    39299817204380409, 12463779785335462, 36561172089555387, 36561165092179356, 11881496387932734, 45806198907896467,
    9739780609952834, 8124121311829188, 50599268415359450, 11459943848374998, 48806198898058706, 12462246634244425,
    11304351321663239, 9739780609952834, 8124121311829188, 37738504851972689, 37738501278094954, 22268551423273385,
    36610798186314211, 36610790151796172, 11776021715645854, 4392317422778766
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
noncomputable def negativeCeiling : ℝ := 5861554209 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 136193035225378313960014479360, coefficient := (-136193035225378313960014479360) }, { argument := 136192459043633014651383447552, coefficient := (-136192459043633014651383447552) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 86864229287696936585903734784, coefficient := (-86864229287696936585903734784) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 116898574544172028950384476160, coefficient := (-116898574544172028950384476160) }, { argument := 116898007562740336404392312832, coefficient := (-116898007562740336404392312832) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 2828341796226200068010541056, coefficient := (-2828341796226200068010541056) }, { argument := 104446899733097534378716692480, coefficient := (-104446899733097534378716692480) }, { argument := 104446874156686876180423376896, coefficient := (-104446874156686876180423376896) }, { argument := 2828367372636858266303856640, coefficient := (-2828367372636858266303856640) }, { argument := 734657687863698944023616028672, coefficient := (-734657687863698944023616028672) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 2674811819535228713303208361984, coefficient := (-2674811819535228713303208361984) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 734657687863698944023616028672, coefficient := (-734657687863698944023616028672) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 136193035225378313960014479360, coefficient := (-136193035225378313960014479360) }, { argument := 136192459043633014651383447552, coefficient := (-136192459043633014651383447552) }, { argument := 415103438753271045756165292032, coefficient := (-415103438753271045756165292032) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 1512524132464717869191931101184, coefficient := (-1512524132464717869191931101184) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 415103438753271045756165292032, coefficient := (-415103438753271045756165292032) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 1560480328437194720324112875520, coefficient := (-1560480328437194720324112875520) }, { argument := 1560463224666818123030555787264, coefficient := (-1560463224666818123030555787264) }, { argument := 109267551280048643326643011584, coefficient := (-109267551280048643326643011584) }, { argument := 116898574544172028950384476160, coefficient := (-116898574544172028950384476160) }, { argument := 116898007562740336404392312832, coefficient := (-116898007562740336404392312832) }, { argument := 72980433878495934018662432768, coefficient := (-72980433878495934018662432768) }, { argument := 138538230826700472841184215040, coefficient := (-138538230826700472841184215040) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 480106232218406066248646393856, coefficient := (-480106232218406066248646393856) }, { argument := 106423251057950324535853056, coefficient := (-106423251057950324535853056) }, { argument := 138538229882005993230555938816, coefficient := (-138538229882005993230555938816) }, { argument := 106593256251333631763546112, coefficient := (-106593256251333631763546112) }, { argument := 95542918681418661963497472, coefficient := (-95542918681418661963497472) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 264375795645329493925736480768, coefficient := (-264375795645329493925736480768) }, { argument := 264375140728268802006311763968, coefficient := (-264375140728268802006311763968) }, { argument := 23859515814008256090293141504, coefficient := (-23859515814008256090293141504) }, { argument := 120989632927989556494383185920, coefficient := (-120989632927989556494383185920) }, { argument := 120988959126074619114805002240, coefficient := (-120988959126074619114805002240) }, { argument := 67835245590216072251112947712, coefficient := (-67835245590216072251112947712) }, { argument := 3249592603124123221610201088, coefficient := (-3249592603124123221610201088) }] }

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

end TermShard8


end Parent2

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 700644926501733536020422667496587264
def positiveArguments : Array ℕ := #[
    55773, 135, 105, 15, 141, 1665,
    117, 105, 1665, 15, 117, 117,
    117, 117, 117, 135, 141, 15,
    63, 273, 9, 9, 21, 273,
    273, 9, 3369, 135, 63, 273,
    21, 135, 21, 273, 273, 9,
    5, 7948212557, 7948199603, 78133683407, 285, 93,
    134417267885, 939, 78133682647, 1881, 843, 285,
    93, 6414338299, 11045, 115427682367, 273305, 8695,
    57712968211, 4465, 4465, 151105, 8225
  ]
def positiveCoefficients : Array ℕ := #[
    4418792307908064900604726742089728, 5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112, 64411567669067442428345057280,
    144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944, 4526218268637171630099922944,
    4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112, 1160568786830044007717928960,
    19497555618744739329661206528, 42244703840613601880932614144, 1392682544196052809261514752, 22282920707136844948184236032, 1624796301562061610805100544, 42244703840613601880932614144,
    42244703840613601880932614144, 22282920707136844948184236032, 521327499044055768266893688832, 41780476325881584277845442560, 19497555618744739329661206528, 42244703840613601880932614144,
    1624796301562061610805100544, 41780476325881584277845442560, 1624796301562061610805100544, 42244703840613601880932614144, 42244703840613601880932614144, 1392682544196052809261514752,
    1584563250285286751870879006720, 75068745155800878963266991161344, 75068622808730040776498794725376, 368975887704364947977336124342272, 176406455598166689173125201920, 7195526478346272847851159552,
    1269535201158068728448566605905920, 145303212111121509766284705792, 368975884115366420996405761933312, 145535325868487518567828291584, 130447931639696946467495215104, 176406455598166689173125201920,
    7195526478346272847851159552, 60581712385969385437504584286208, 427282741684594535508150845440, 2180367273620977417569934904393728, 10572975076152839250978285813760, 336371520049574421570246410240,
    2180334293652381682199084398542848, 345462642213076432964036853760, 345462642213076432964036853760, 5845591551131793326207255183360, 318189275722570398782665523200
  ]
def positiveScales : Array ℕ := #[
    15, 7, 6, 3, 7, 10,
    6, 6, 10, 3, 6, 6,
    6, 6, 6, 7, 7, 3,
    5, 8, 3, 3, 4, 8,
    8, 3, 11, 7, 5, 8,
    4, 7, 4, 8, 8, 3,
    2, 32, 32, 36, 8, 6,
    36, 9, 36, 10, 9, 8,
    6, 32, 13, 36, 18, 13,
    35, 12, 12, 17, 13
  ]
def negativeArguments : Array ℕ := #[
    3, 3, 5, 1895, 6337
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 950737950171172051122527404032, 1584563250285286751870879006720, 150137367964530919739765785886720, 2008275463411572429321152053116928
  ]
def negativeScales : Array ℕ := #[
    1, 1, 2, 10, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15767279254393674, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793, 10701306461953989,
    6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793, 3906890595303263,
    5977279922488012, 8092757140919852, 3169925001442312, 3169925001442312, 4392317422778759, 8092757140919852,
    8092757140919852, 3169925001442312, 11718104713114918, 7076815597050830, 5977279922488012, 8092757140919852,
    4392317422778759, 7076815597050830, 4392317422778759, 8092757140919852, 8092757140919852, 3169925001442312,
    2321928094887362, 32887983308494047, 32887980957187186, 36185225576730170, 8154818109052103, 6539158811107971,
    36967927528419129, 9874981347482478, 36185225562697192, 10877284133344468, 9719388820935039, 8154818109052103,
    6539158811107971, 32578653299037680, 13431105798242635, 36748198302603157, 18060152328038218, 13085970312193949,
    35748176480409460, 12124444460008585, 12124444460008585, 17205191873892946, 13005799963509966
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 1584962500724866, 2321928094887363, 10887982136573879, 12629584300206413
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 1857465009441 / 500000000000
noncomputable def negativeCeiling : ℝ := 65010527969 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4418792307908064900604726742089728, coefficient := 4418792307908064900604726742089728 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 19497555618744739329661206528, coefficient := 19497555618744739329661206528 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 521327499044055768266893688832, coefficient := 521327499044055768266893688832 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 19497555618744739329661206528, coefficient := 19497555618744739329661206528 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 1624796301562061610805100544, coefficient := 1624796301562061610805100544 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 75068745155800878963266991161344, coefficient := 75068745155800878963266991161344 }, { argument := 75068622808730040776498794725376, coefficient := 75068622808730040776498794725376 }, { argument := 150137367964530919739765785886720, coefficient := (-150137367964530919739765785886720) }, { argument := 368975887704364947977336124342272, coefficient := 368975887704364947977336124342272 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 1269535201158068728448566605905920, coefficient := 1269535201158068728448566605905920 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 368975884115366420996405761933312, coefficient := 368975884115366420996405761933312 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 2008275463411572429321152053116928, coefficient := (-2008275463411572429321152053116928) }, { argument := 60581712385969385437504584286208, coefficient := 60581712385969385437504584286208 }, { argument := 427282741684594535508150845440, coefficient := 427282741684594535508150845440 }, { argument := 2180367273620977417569934904393728, coefficient := 2180367273620977417569934904393728 }, { argument := 10572975076152839250978285813760, coefficient := 10572975076152839250978285813760 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 2180334293652381682199084398542848, coefficient := 2180334293652381682199084398542848 }, { argument := 345462642213076432964036853760, coefficient := 345462642213076432964036853760 }, { argument := 345462642213076432964036853760, coefficient := 345462642213076432964036853760 }, { argument := 5845591551131793326207255183360, coefficient := 5845591551131793326207255183360 }, { argument := 318189275722570398782665523200, coefficient := 318189275722570398782665523200 }] }

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

end TermShard9


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
