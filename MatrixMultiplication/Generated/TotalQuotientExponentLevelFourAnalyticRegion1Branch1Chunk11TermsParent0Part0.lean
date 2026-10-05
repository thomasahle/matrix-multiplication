import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

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
def constantNumerator : ℤ := (-824693112781955035101160986902528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 21516779525, 85941288965, 42823843825, 85941288965, 14957312475735,
    190460722317, 568187246676385, 158906823551, 3907004493, 39694482193, 80036300657,
    1876973855169, 190460722317, 3907004493, 10385448269513, 986988112791863, 988426465,
    5115073947, 34250980367, 122031705575, 246734936571827, 34250980367, 3964712915,
    2005999423, 988426465, 3906419929, 122031705575, 3906419929, 2596348495181,
    5115073947, 26089213473, 13580614198581, 79305, 536096944914339, 12453,
    5583, 158091, 80613, 12453, 2478723, 158673,
    54322512602985, 158091, 5583, 158673, 5583, 158091,
    40431, 26089213473, 21516779515, 85941288955, 42823843855, 85941288955,
    55066890921817, 683918318879, 2101628153778735, 570601106455, 3507342697, 71267184471,
    143698980829, 6910515434639, 683918318879, 3507342697
  ]
def negativeCoefficients : Array ℕ := #[
    79228162514264337593543950336, 99228631297027192752019865600, 99083560181379614681952419840, 98745060911535265851795046400, 99083560181379614681952419840, 33680873446092108496927457280,
    219586262542222518152847163392, 1279443936204217788926504468480, 183207094100713666041689931776, 9008938997150542667590926336, 183058488538173019018831593472, 184551144353268830303854526464,
    33812555018893086909630775296, 219586262542222518152847163392, 9008938997150542667590926336, 11692975239163577328428122112, 1111249824247135820818008768512, 4558312508884107885134479360,
    5897278751150523444753334272, 78977383637962431657498640384, 140692977601268756304311091200, 1111195368404163042968644616192, 78977383637962431657498640384, 4571002779295998203175895040,
    4625519746011253751410589696, 4558312508884107885134479360, 4503795542168852336899784704, 140692977601268756304311091200, 4503795542168852336899784704, 11692914115421099629557579776,
    5897278751150523444753334272, 234990744150784247611785216, 30580824522095929383702233088, 1498029095695908854688645120, 301795750168834805131816992768, 940922076978811069538500608,
    52729944147722458456129536, 1493127279286690162956828672, 1522736517134282838446702592, 940922076978811069538500608, 23410876831036191186056380416, 1498624113872750429985570816,
    30580855939579039839493816320, 1493127279286690162956828672, 52729944147722458456129536, 1498624113872750429985570816, 52729944147722458456129536, 1493127279286690162956828672,
    1527439994151221005079543808, 234990744150784247611785216, 99228631250910332567745986560, 99083560169850399635883950080, 98745060980710556128205864960, 99083560169850399635883950080,
    123999614717973395090614255616, 788504137230162037658724859904, 4732445885114627205497125601280, 657858286184430264274470830080, 32349526555176612779761074176, 657323756395192318146084077568,
    662694580751364555145442492416, 124488778945513046424500043776, 788504137230162037658724859904, 32349526555176612779761074176
  ]
def negativeScales : Array ℕ := #[
    0, 34, 36, 35, 36, 43,
    37, 49, 37, 31, 35, 36,
    40, 37, 31, 43, 49, 29,
    32, 34, 36, 47, 34, 31,
    30, 29, 31, 36, 31, 41,
    32, 34, 43, 16, 48, 13,
    12, 17, 16, 13, 21, 17,
    45, 17, 12, 17, 12, 17,
    15, 34, 34, 36, 35, 36,
    45, 39, 50, 39, 31, 36,
    37, 42, 39, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 34324743110829666, 36322632363982545, 35317695245259829, 36322632363982545, 43765916209463315,
    37470702552970432, 49013359778107474, 37209390119937827, 31863415770820500, 35208219425610800, 36219935435118533,
    40771545693660196, 37470702552970432, 31863415770820500, 43239628722442971, 49810026038293876, 29880558401338675,
    32252107950691772, 34995426253855142, 36828465074110209, 47809955338529373, 34995426253855142, 31884569261402776,
    30901674049464239, 29880558401338675, 31863199899372804, 36828465074110209, 31863199899372804, 41239621180893551,
    32252107950691772, 34602734399907192, 43626613962114446, 16275124206989461, 48929487249321402, 13604205717331114,
    12446824840780350, 17270395712943008, 16298724892287697, 13604205717331114, 21241165627011478, 17275697132666352,
    45626615444279317, 17270395712943008, 12446824840780350, 17275697132666352, 12446824840780350, 17270395712943008,
    15303174266493198, 34602734399907192, 34324743110159168, 36322632363814675, 35317695246270501, 36322632363814675,
    45646250389741370, 39315033076496636, 50900428860020764, 39053691588219339, 31707731255039472, 36052518878292293,
    37064258873418715, 42651930459597558, 39315033076496636, 31707731255039472
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
noncomputable def negativeCeiling : ℝ := 1001186989 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 99228631297027192752019865600, coefficient := (-99228631297027192752019865600) }, { argument := 99083560181379614681952419840, coefficient := (-99083560181379614681952419840) }, { argument := 98745060911535265851795046400, coefficient := (-98745060911535265851795046400) }, { argument := 99083560181379614681952419840, coefficient := (-99083560181379614681952419840) }, { argument := 33680873446092108496927457280, coefficient := (-33680873446092108496927457280) }, { argument := 219586262542222518152847163392, coefficient := (-219586262542222518152847163392) }, { argument := 1279443936204217788926504468480, coefficient := (-1279443936204217788926504468480) }, { argument := 183207094100713666041689931776, coefficient := (-183207094100713666041689931776) }, { argument := 9008938997150542667590926336, coefficient := (-9008938997150542667590926336) }, { argument := 183058488538173019018831593472, coefficient := (-183058488538173019018831593472) }, { argument := 184551144353268830303854526464, coefficient := (-184551144353268830303854526464) }, { argument := 33812555018893086909630775296, coefficient := (-33812555018893086909630775296) }, { argument := 219586262542222518152847163392, coefficient := (-219586262542222518152847163392) }, { argument := 9008938997150542667590926336, coefficient := (-9008938997150542667590926336) }, { argument := 11692975239163577328428122112, coefficient := (-11692975239163577328428122112) }, { argument := 1111249824247135820818008768512, coefficient := (-1111249824247135820818008768512) }, { argument := 4558312508884107885134479360, coefficient := (-4558312508884107885134479360) }, { argument := 5897278751150523444753334272, coefficient := (-5897278751150523444753334272) }, { argument := 78977383637962431657498640384, coefficient := (-78977383637962431657498640384) }, { argument := 140692977601268756304311091200, coefficient := (-140692977601268756304311091200) }, { argument := 1111195368404163042968644616192, coefficient := (-1111195368404163042968644616192) }, { argument := 78977383637962431657498640384, coefficient := (-78977383637962431657498640384) }, { argument := 4571002779295998203175895040, coefficient := (-4571002779295998203175895040) }, { argument := 4625519746011253751410589696, coefficient := (-4625519746011253751410589696) }, { argument := 4558312508884107885134479360, coefficient := (-4558312508884107885134479360) }, { argument := 4503795542168852336899784704, coefficient := (-4503795542168852336899784704) }, { argument := 140692977601268756304311091200, coefficient := (-140692977601268756304311091200) }, { argument := 4503795542168852336899784704, coefficient := (-4503795542168852336899784704) }, { argument := 11692914115421099629557579776, coefficient := (-11692914115421099629557579776) }, { argument := 5897278751150523444753334272, coefficient := (-5897278751150523444753334272) }, { argument := 234990744150784247611785216, coefficient := (-234990744150784247611785216) }, { argument := 30580824522095929383702233088, coefficient := (-30580824522095929383702233088) }, { argument := 1498029095695908854688645120, coefficient := (-1498029095695908854688645120) }, { argument := 301795750168834805131816992768, coefficient := (-301795750168834805131816992768) }, { argument := 940922076978811069538500608, coefficient := (-940922076978811069538500608) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 1522736517134282838446702592, coefficient := (-1522736517134282838446702592) }, { argument := 940922076978811069538500608, coefficient := (-940922076978811069538500608) }, { argument := 23410876831036191186056380416, coefficient := (-23410876831036191186056380416) }, { argument := 1498624113872750429985570816, coefficient := (-1498624113872750429985570816) }, { argument := 30580855939579039839493816320, coefficient := (-30580855939579039839493816320) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1498624113872750429985570816, coefficient := (-1498624113872750429985570816) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 1527439994151221005079543808, coefficient := (-1527439994151221005079543808) }, { argument := 234990744150784247611785216, coefficient := (-234990744150784247611785216) }, { argument := 99228631250910332567745986560, coefficient := (-99228631250910332567745986560) }, { argument := 99083560169850399635883950080, coefficient := (-99083560169850399635883950080) }, { argument := 98745060980710556128205864960, coefficient := (-98745060980710556128205864960) }, { argument := 99083560169850399635883950080, coefficient := (-99083560169850399635883950080) }, { argument := 123999614717973395090614255616, coefficient := (-123999614717973395090614255616) }, { argument := 788504137230162037658724859904, coefficient := (-788504137230162037658724859904) }, { argument := 4732445885114627205497125601280, coefficient := (-4732445885114627205497125601280) }, { argument := 657858286184430264274470830080, coefficient := (-657858286184430264274470830080) }, { argument := 32349526555176612779761074176, coefficient := (-32349526555176612779761074176) }, { argument := 657323756395192318146084077568, coefficient := (-657323756395192318146084077568) }, { argument := 662694580751364555145442492416, coefficient := (-662694580751364555145442492416) }, { argument := 124488778945513046424500043776, coefficient := (-124488778945513046424500043776) }, { argument := 788504137230162037658724859904, coefficient := (-788504137230162037658724859904) }, { argument := 32349526555176612779761074176, coefficient := (-32349526555176612779761074176) }] }

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
def constantNumerator : ℤ := (-9289133647961823650765359277932544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1632148486218043, 154509830374858437, 38991684029, 50443297455, 675542926469, 601592962433,
    38625523864032017, 675542926469, 39087498421, 9890029777, 38991684029, 19259531671,
    601592962433, 19259531671, 408034996903151, 50443297455, 1697536554993, 1253630334723885,
    73119, 25640159238852669, 367365, 82251, 2332023, 2379297,
    367365, 18288759, 585375, 2507264732832345, 2332023, 82251,
    585375, 82251, 2332023, 1193259, 1697536554993, 79347,
    2339409, 2062137, 145027, 323779, 145027, 4110607,
    2096747, 323779, 64468603, 4126929, 2339409, 4110607,
    145027, 4126929, 145027, 4110607, 1051569, 79347,
    20711951345317, 813632687253023, 813632634820955, 20712052300257, 934723432805, 47621908885,
    35505840261699, 79464771637, 3907559951, 39700162113
  ]
def negativeCoefficients : Array ℕ := #[
    459408957146556098813737566208, 43490650906330687572847909404672, 179817404071477780632584585216, 232628649596597339360140984320, 3115391868844608285847612030976, 5548715707273157834138781220864,
    43488473720261198141696516292608, 3115391868844608285847612030976, 180259269963428301600754499584, 182438848177685748331558469632, 179817404071477780632584585216, 177637825857220333901780615168,
    5548715707273157834138781220864, 177637825857220333901780615168, 459406565001788083234326708224, 232628649596597339360140984320, 30580099986057081164358746112, 5645849108322838658484755496960,
    22098861751100517656335220736, 57736505796908530226856210726912, 13878657303835257711435448320, 776838731165022376943419392, 22025334504962237280357974016, 22471824811184596496022503424,
    13878657303835257711435448320, 345464890059522278915158573056, 22114842239278548535738368000, 5645858258251467574995383746560, 22025334504962237280357974016, 776838731165022376943419392,
    22114842239278548535738368000, 776838731165022376943419392, 22025334504962237280357974016, 22540025227930199912198701056, 30580099986057081164358746112, 1498822453265030955084546048,
    22095093302647187679454691328, 38952666607541446288141713408, 1369741287822272072813379584, 24464049559312813722324434944, 1369741287822272072813379584, 38823585442098687405870546944,
    39606431023429919971525787648, 24464049559312813722324434944, 608888740009258916065235173376, 38977742373565484104226439168, 22095093302647187679454691328, 38823585442098687405870546944,
    1369741287822272072813379584, 38977742373565484104226439168, 1369741287822272072813379584, 38823585442098687405870546944, 39727153600197999581768712192, 1498822453265030955084546048,
    11659792045110685565299195904, 458034483391146211689864626176, 458034453874515973306801192960, 11659848877689456216646877184, 33676960829400550853564170240, 219617291375777497752839127040,
    1279232711776511764638971461632, 183233288157939076828888039424, 9010219796096754487606116352, 183084682545822805107935281152
  ]
def negativeScales : Array ℕ := #[
    50, 57, 35, 35, 39, 39,
    55, 39, 35, 33, 35, 34,
    39, 34, 48, 35, 40, 50,
    16, 54, 18, 16, 21, 21,
    18, 24, 19, 51, 21, 16,
    19, 16, 21, 20, 40, 16,
    21, 20, 17, 18, 17, 21,
    20, 18, 25, 21, 21, 21,
    17, 21, 17, 21, 20, 16,
    44, 49, 49, 44, 39, 35,
    45, 36, 31, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    50535693737107018, 57100476242683360, 35182447414145747, 35553943535930707, 39297256490345676, 39129996733910850,
    55100404018099365, 39297256490345676, 35185988204744042, 33203327718657762, 35182447414145747, 34164853570843127,
    39129996733910850, 34164853570843127, 48535686224967071, 35553943535930707, 40626579780664151, 50155033418273631,
    16157958719298466, 54509254740076415, 18486854657413929, 16327745598655941, 21153150586774380, 21182103939314677,
    18486854657413929, 24124453847264900, 19159001607361153, 51155035756371180, 21153150586774380, 16327745598655941,
    19159001607361153, 16327745598655941, 21153150586774380, 20186475787094054, 40626579780664151, 16275888057342849,
    21157712680133062, 20975708767995790, 17145961989435072, 18304649891274507, 17145961989435072, 21970920031835689,
    20999721384770933, 18304649891274507, 25942093394726026, 21976637203880006, 21157712680133062, 21970920031835689,
    17145961989435072, 21976637203880006, 17145961989435072, 21970920031835689, 20004112086718483, 16275888057342849,
    44235528714838848, 49531370968276260, 49531370875306191, 44235535746857894, 39765748605715271, 35470906399883644,
    45013121582761220, 36209596374697694, 31863620863898367, 35208425847404166
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
noncomputable def negativeCeiling : ℝ := 114868966453 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 459408957146556098813737566208, coefficient := (-459408957146556098813737566208) }, { argument := 43490650906330687572847909404672, coefficient := (-43490650906330687572847909404672) }, { argument := 179817404071477780632584585216, coefficient := (-179817404071477780632584585216) }, { argument := 232628649596597339360140984320, coefficient := (-232628649596597339360140984320) }, { argument := 3115391868844608285847612030976, coefficient := (-3115391868844608285847612030976) }, { argument := 5548715707273157834138781220864, coefficient := (-5548715707273157834138781220864) }, { argument := 43488473720261198141696516292608, coefficient := (-43488473720261198141696516292608) }, { argument := 3115391868844608285847612030976, coefficient := (-3115391868844608285847612030976) }, { argument := 180259269963428301600754499584, coefficient := (-180259269963428301600754499584) }, { argument := 182438848177685748331558469632, coefficient := (-182438848177685748331558469632) }, { argument := 179817404071477780632584585216, coefficient := (-179817404071477780632584585216) }, { argument := 177637825857220333901780615168, coefficient := (-177637825857220333901780615168) }, { argument := 5548715707273157834138781220864, coefficient := (-5548715707273157834138781220864) }, { argument := 177637825857220333901780615168, coefficient := (-177637825857220333901780615168) }, { argument := 459406565001788083234326708224, coefficient := (-459406565001788083234326708224) }, { argument := 232628649596597339360140984320, coefficient := (-232628649596597339360140984320) }, { argument := 30580099986057081164358746112, coefficient := (-30580099986057081164358746112) }, { argument := 5645849108322838658484755496960, coefficient := (-5645849108322838658484755496960) }, { argument := 22098861751100517656335220736, coefficient := (-22098861751100517656335220736) }, { argument := 57736505796908530226856210726912, coefficient := (-57736505796908530226856210726912) }, { argument := 13878657303835257711435448320, coefficient := (-13878657303835257711435448320) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 22471824811184596496022503424, coefficient := (-22471824811184596496022503424) }, { argument := 13878657303835257711435448320, coefficient := (-13878657303835257711435448320) }, { argument := 345464890059522278915158573056, coefficient := (-345464890059522278915158573056) }, { argument := 22114842239278548535738368000, coefficient := (-22114842239278548535738368000) }, { argument := 5645858258251467574995383746560, coefficient := (-5645858258251467574995383746560) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22114842239278548535738368000, coefficient := (-22114842239278548535738368000) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 22540025227930199912198701056, coefficient := (-22540025227930199912198701056) }, { argument := 30580099986057081164358746112, coefficient := (-30580099986057081164358746112) }, { argument := 1498822453265030955084546048, coefficient := (-1498822453265030955084546048) }, { argument := 22095093302647187679454691328, coefficient := (-22095093302647187679454691328) }, { argument := 38952666607541446288141713408, coefficient := (-38952666607541446288141713408) }, { argument := 1369741287822272072813379584, coefficient := (-1369741287822272072813379584) }, { argument := 24464049559312813722324434944, coefficient := (-24464049559312813722324434944) }, { argument := 1369741287822272072813379584, coefficient := (-1369741287822272072813379584) }, { argument := 38823585442098687405870546944, coefficient := (-38823585442098687405870546944) }, { argument := 39606431023429919971525787648, coefficient := (-39606431023429919971525787648) }, { argument := 24464049559312813722324434944, coefficient := (-24464049559312813722324434944) }, { argument := 608888740009258916065235173376, coefficient := (-608888740009258916065235173376) }, { argument := 38977742373565484104226439168, coefficient := (-38977742373565484104226439168) }, { argument := 22095093302647187679454691328, coefficient := (-22095093302647187679454691328) }, { argument := 38823585442098687405870546944, coefficient := (-38823585442098687405870546944) }, { argument := 1369741287822272072813379584, coefficient := (-1369741287822272072813379584) }, { argument := 38977742373565484104226439168, coefficient := (-38977742373565484104226439168) }, { argument := 1369741287822272072813379584, coefficient := (-1369741287822272072813379584) }, { argument := 38823585442098687405870546944, coefficient := (-38823585442098687405870546944) }, { argument := 39727153600197999581768712192, coefficient := (-39727153600197999581768712192) }, { argument := 1498822453265030955084546048, coefficient := (-1498822453265030955084546048) }, { argument := 11659792045110685565299195904, coefficient := (-11659792045110685565299195904) }, { argument := 458034483391146211689864626176, coefficient := (-458034483391146211689864626176) }, { argument := 458034453874515973306801192960, coefficient := (-458034453874515973306801192960) }, { argument := 11659848877689456216646877184, coefficient := (-11659848877689456216646877184) }, { argument := 33676960829400550853564170240, coefficient := (-33676960829400550853564170240) }, { argument := 219617291375777497752839127040, coefficient := (-219617291375777497752839127040) }, { argument := 1279232711776511764638971461632, coefficient := (-1279232711776511764638971461632) }, { argument := 183233288157939076828888039424, coefficient := (-183233288157939076828888039424) }, { argument := 9010219796096754487606116352, coefficient := (-9010219796096754487606116352) }, { argument := 183084682545822805107935281152, coefficient := (-183084682545822805107935281152) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
