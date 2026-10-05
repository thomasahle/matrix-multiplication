import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-943693674554082861414433240907776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 19809700467, 18845010317, 19809700467, 18845010317, 57610250199669,
    20783561751, 309231618627979, 385693263, 1881941913, 49336831341, 19930621131,
    57683392135797, 20783561751, 1846228077, 9565937361843, 598900113030221, 70443055,
    2322836935, 62342429859, 5987615643, 299450086068677, 62342429859, 70443055,
    2225980767, 2065081047, 2225980767, 5987615643, 2065081047, 4782939127355,
    2322836935, 139044906567, 34261635175875, 70785, 692541265117837, 52215,
    1275, 70785, 57915, 52215, 983295, 14805,
    17130820126211, 70785, 1275, 14805, 1275, 17745,
    57915, 563714957509, 19809695117, 18845005427, 19809695117, 18845005427,
    99026178432395, 36332372969, 533521450395253, 681560497, 3300120679, 87185666707,
    34970721077, 99159194926475, 36332372969, 3235171219
  ]
def negativeCoefficients : Array ℕ := #[
    79228162514264337593543950336, 91356118672898396767458951168, 86907270596028777166241005568, 91356118672898396767458951168, 86907270596028777166241005568, 129726750665975175590719782912,
    191694522280417880824828919808, 1392655402424141553939024707584, 227673117232478383265342816256, 8678925207674591643646820352, 227525975288799855074831499264, 183827533616812305497192398848,
    129891451664120784300231622656, 191694522280417880824828919808, 8514224209528982934134980608, 21540575969122820180687192064, 1348603162937525615802405879808, 5197780029420983994044907520,
    5356097308113113619491717120, 143751856067770205944852512768, 110452013378160856294477529088, 1348603296034956692671579553792, 143751856067770205944852512768, 5197780029420983994044907520,
    5132762190231086530176221184, 4761752695684645753133727744, 5132762190231086530176221184, 110452013378160856294477529088, 4761752695684645753133727744, 21540442871691743311513518080,
    5356097308113113619491717120, 313101294701453316106223616, 38575171852793632046186496000, 1337090845959711345805885440, 389866072940422824100987142144, 986313463612154099332546560,
    48168138125270381179699200, 1337090845959711345805885440, 1093983419421582010204815360, 986313463612154099332546560, 18573917403093231161604833280, 1118634172462161558220308480,
    38575177568477426428388835328, 1337090845959711345805885440, 48168138125270381179699200, 1118634172462161558220308480, 48168138125270381179699200, 1340774291816349669072568320,
    1093983419421582010204815360, 317343309072588423255031808, 91356094000378198180933664768, 86907248044884147056314155008, 91356094000378198180933664768, 86907248044884147056314155008,
    445974260288058369721153617920, 670213985749705856690268667904, 4805534010388455953312541310976, 804644611770194344515079241728, 30438240788934795763889733632, 804145840319884204157494624256,
    645095941780499458273870610432, 446573313321231187508304281600, 670213985749705856690268667904, 29839187755761977976739069952
  ]
def negativeScales : Array ℕ := #[
    0, 34, 34, 34, 34, 45,
    34, 48, 28, 30, 35, 34,
    45, 34, 30, 43, 49, 26,
    31, 35, 32, 48, 35, 26,
    31, 30, 31, 32, 30, 42,
    31, 37, 44, 16, 49, 15,
    10, 16, 15, 15, 19, 13,
    43, 16, 10, 13, 10, 14,
    15, 39, 34, 34, 34, 34,
    46, 35, 48, 29, 31, 36,
    35, 46, 35, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 34205488014964692, 34133463533702408, 34205488014964692, 34133463533702408, 45711390757044177,
    34274723863951956, 48135681169372794, 28522878705373701, 30809574954080319, 35521946010369089, 34214267620849387,
    45713221239988187, 34274723863951956, 30781933644268308, 43121043483176170, 49089308733018759, 26069954142060058,
    31113240733348598, 35859495337499207, 32479334468880554, 48089308875402374, 35859495337499207, 26069954142060058,
    31051793981493810, 30943551266675676, 31051793981493810, 32479334468880554, 30943551266675676, 42121034568855713,
    31113240733348598, 37016759941231506, 44961659253553293, 16111156051745362, 49298893365227053, 15672176694369290,
    10316281531746221, 16111156051745362, 15821649435548504, 15672176694369290, 19907264786299424, 13853796871926908,
    43961659467317469, 16111156051745362, 10316281531746221, 13853796871926908, 10316281531746221, 14115124953948308,
    15821649435548504, 39036174891952844, 34205487625336413, 34133463159344445, 34205487625336413, 34133463159344445,
    46492875198143036, 35080536544156552, 48922539611146669, 29344266479002805, 31619871635985697, 36343371924811463,
    35025428492792776, 46494811791766775, 35080536544156552, 31591194921777402
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
noncomputable def negativeCeiling : ℝ := 214735539 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 91356118672898396767458951168, coefficient := (-91356118672898396767458951168) }, { argument := 86907270596028777166241005568, coefficient := (-86907270596028777166241005568) }, { argument := 91356118672898396767458951168, coefficient := (-91356118672898396767458951168) }, { argument := 86907270596028777166241005568, coefficient := (-86907270596028777166241005568) }, { argument := 129726750665975175590719782912, coefficient := (-129726750665975175590719782912) }, { argument := 191694522280417880824828919808, coefficient := (-191694522280417880824828919808) }, { argument := 1392655402424141553939024707584, coefficient := (-1392655402424141553939024707584) }, { argument := 227673117232478383265342816256, coefficient := (-227673117232478383265342816256) }, { argument := 8678925207674591643646820352, coefficient := (-8678925207674591643646820352) }, { argument := 227525975288799855074831499264, coefficient := (-227525975288799855074831499264) }, { argument := 183827533616812305497192398848, coefficient := (-183827533616812305497192398848) }, { argument := 129891451664120784300231622656, coefficient := (-129891451664120784300231622656) }, { argument := 191694522280417880824828919808, coefficient := (-191694522280417880824828919808) }, { argument := 8514224209528982934134980608, coefficient := (-8514224209528982934134980608) }, { argument := 21540575969122820180687192064, coefficient := (-21540575969122820180687192064) }, { argument := 1348603162937525615802405879808, coefficient := (-1348603162937525615802405879808) }, { argument := 5197780029420983994044907520, coefficient := (-5197780029420983994044907520) }, { argument := 5356097308113113619491717120, coefficient := (-5356097308113113619491717120) }, { argument := 143751856067770205944852512768, coefficient := (-143751856067770205944852512768) }, { argument := 110452013378160856294477529088, coefficient := (-110452013378160856294477529088) }, { argument := 1348603296034956692671579553792, coefficient := (-1348603296034956692671579553792) }, { argument := 143751856067770205944852512768, coefficient := (-143751856067770205944852512768) }, { argument := 5197780029420983994044907520, coefficient := (-5197780029420983994044907520) }, { argument := 5132762190231086530176221184, coefficient := (-5132762190231086530176221184) }, { argument := 4761752695684645753133727744, coefficient := (-4761752695684645753133727744) }, { argument := 5132762190231086530176221184, coefficient := (-5132762190231086530176221184) }, { argument := 110452013378160856294477529088, coefficient := (-110452013378160856294477529088) }, { argument := 4761752695684645753133727744, coefficient := (-4761752695684645753133727744) }, { argument := 21540442871691743311513518080, coefficient := (-21540442871691743311513518080) }, { argument := 5356097308113113619491717120, coefficient := (-5356097308113113619491717120) }, { argument := 313101294701453316106223616, coefficient := (-313101294701453316106223616) }, { argument := 38575171852793632046186496000, coefficient := (-38575171852793632046186496000) }, { argument := 1337090845959711345805885440, coefficient := (-1337090845959711345805885440) }, { argument := 389866072940422824100987142144, coefficient := (-389866072940422824100987142144) }, { argument := 986313463612154099332546560, coefficient := (-986313463612154099332546560) }, { argument := 48168138125270381179699200, coefficient := (-48168138125270381179699200) }, { argument := 1337090845959711345805885440, coefficient := (-1337090845959711345805885440) }, { argument := 1093983419421582010204815360, coefficient := (-1093983419421582010204815360) }, { argument := 986313463612154099332546560, coefficient := (-986313463612154099332546560) }, { argument := 18573917403093231161604833280, coefficient := (-18573917403093231161604833280) }, { argument := 1118634172462161558220308480, coefficient := (-1118634172462161558220308480) }, { argument := 38575177568477426428388835328, coefficient := (-38575177568477426428388835328) }, { argument := 1337090845959711345805885440, coefficient := (-1337090845959711345805885440) }, { argument := 48168138125270381179699200, coefficient := (-48168138125270381179699200) }, { argument := 1118634172462161558220308480, coefficient := (-1118634172462161558220308480) }, { argument := 48168138125270381179699200, coefficient := (-48168138125270381179699200) }, { argument := 1340774291816349669072568320, coefficient := (-1340774291816349669072568320) }, { argument := 1093983419421582010204815360, coefficient := (-1093983419421582010204815360) }, { argument := 317343309072588423255031808, coefficient := (-317343309072588423255031808) }, { argument := 91356094000378198180933664768, coefficient := (-91356094000378198180933664768) }, { argument := 86907248044884147056314155008, coefficient := (-86907248044884147056314155008) }, { argument := 91356094000378198180933664768, coefficient := (-91356094000378198180933664768) }, { argument := 86907248044884147056314155008, coefficient := (-86907248044884147056314155008) }, { argument := 445974260288058369721153617920, coefficient := (-445974260288058369721153617920) }, { argument := 670213985749705856690268667904, coefficient := (-670213985749705856690268667904) }, { argument := 4805534010388455953312541310976, coefficient := (-4805534010388455953312541310976) }, { argument := 804644611770194344515079241728, coefficient := (-804644611770194344515079241728) }, { argument := 30438240788934795763889733632, coefficient := (-30438240788934795763889733632) }, { argument := 804145840319884204157494624256, coefficient := (-804145840319884204157494624256) }, { argument := 645095941780499458273870610432, coefficient := (-645095941780499458273870610432) }, { argument := 446573313321231187508304281600, coefficient := (-446573313321231187508304281600) }, { argument := 670213985749705856690268667904, coefficient := (-670213985749705856690268667904) }, { argument := 29839187755761977976739069952, coefficient := (-29839187755761977976739069952) }] }

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
def constantNumerator : ℤ := (-9952857599067613973422548617003008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    351208661223501, 22152424766543795, 10133208295, 41609993729, 1136000794245, 212620014249,
    11076213535463483, 1136000794245, 10133208295, 40039420953, 37068514653, 40039420953,
    212620014249, 37068514653, 175603178420165, 41609993729, 34270698936825, 4600804368334437,
    398307, 95366139943119503, 272583, 14595, 398307, 344253,
    272583, 5376369, 21789, 1150201294697729, 398307, 14595,
    21789, 14595, 199563, 344253, 68741212978349, 142551,
    808815, 2130219, 69915, 832593, 151305, 2130219,
    1661751, 832593, 30283623, 857079, 808815, 2130219,
    151305, 857079, 151305, 2137317, 1661751, 77013,
    19129104494517, 702458552761419, 1404871519465845, 38303837992587, 57610250199669, 20783561751,
    309231618627979, 385693263, 1881941913, 49336831341
  ]
def negativeCoefficients : Array ℕ := #[
    790851597907724935691394613248, 49882825961979791003734937436160, 186924700063455719855981854720, 191892226306880589127290454016, 5238878979742074364804705812480, 3922146987799781170881320976384,
    49882831150989386120955919597568, 5238878979742074364804705812480, 186924700063455719855981854720, 184649237794878699352476352512, 170948350749110856535938957312, 184649237794878699352476352512,
    3922146987799781170881320976384, 170948350749110856535938957312, 790846408898129818470412451840, 191892226306880589127290454016, 38585376740402880859393228800, 5180045209708880174926358642688,
    30095226027077756418105802752, 53686364038949446038948923047936, 20595789168000904020558348288, 1102767021079719550302289920, 30095226027077756418105802752, 26011021261237183580007825408,
    20595789168000904020558348288, 406226956242230265086616797184, 26341284683583155087672868864, 5180046122201754381027412803584, 30095226027077756418105802752, 1102767021079719550302289920,
    26341284683583155087672868864, 1102767021079719550302289920, 30157107917469280248986075136, 26011021261237183580007825408, 38697862644286057489931173888, 1346356128999101589715156992,
    30556166774737696748124241920, 40238699227088371029897117696, 1320657010599324980462223360, 31454474216575092139254349824, 1429035321381183338116546560, 40238699227088371029897117696,
    31389588901100463214018166784, 31454474216575092139254349824, 572041464940241175181296402432, 32379529142171461200874831872, 30556166774737696748124241920, 40238699227088371029897117696,
    1429035321381183338116546560, 32379529142171461200874831872, 1429035321381183338116546560, 40372776656270005996804374528, 31389588901100463214018166784, 1454734439780959947369480192,
    21537456968359510360989892608, 790898019114886128088651923456, 790872356446225257464479088640, 21563143813784332590743814144, 129726750665975175590719782912, 191694522280417880824828919808,
    1392655402424141553939024707584, 227673117232478383265342816256, 8678925207674591643646820352, 227525975288799855074831499264
  ]
def negativeScales : Array ℕ := #[
    48, 54, 33, 35, 40, 37,
    53, 40, 33, 35, 35, 35,
    37, 35, 47, 35, 44, 52,
    18, 56, 18, 13, 18, 18,
    18, 22, 14, 50, 18, 13,
    14, 13, 17, 18, 45, 17,
    19, 21, 16, 19, 17, 21,
    20, 19, 24, 19, 19, 21,
    17, 19, 17, 21, 20, 16,
    44, 49, 50, 45, 45, 34,
    48, 28, 30, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48319321752311478, 54298314140554057, 33238371969851290, 35276211019829204, 40047100982164291, 37629486450138011,
    53298314290628915, 40047100982164291, 33238371969851290, 35220702059054624, 35109475255946427, 35220702059054624,
    37629486450138011, 35109475255946427, 47319312286334562, 35276211019829204, 44962040861621633, 52030807535949336,
    18603521308843975, 56404326641794965, 18056336063797573, 13833186591641834, 18603521308843975, 18393109701248078,
    18056336063797573, 22358200728311561, 14411312365441260, 50030807790087819, 18603521308843975, 13833186591641834,
    14411312365441260, 13833186591641834, 17606484736879050, 18393109701248078, 45966240556334345, 17121118634301809,
    19625450227654563, 21022570325584000, 16093314393147463, 19667251903584665, 17207100137840871, 21022570325584000,
    20664272791428176, 19667251903584665, 24852034479376090, 19709068663292793, 19625450227654563, 21022570325584000,
    17207100137840871, 19709068663292793, 17207100137840871, 21027369469091250, 20664272791428176, 16232814376688060,
    44120834570807856, 49319406432775012, 50319359620158734, 45122554189013891, 45711390757044177, 34274723863951956,
    48135681169372794, 28522878705373701, 30809574954080319, 35521946010369089
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
noncomputable def negativeCeiling : ℝ := 120137300519 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 790851597907724935691394613248, coefficient := (-790851597907724935691394613248) }, { argument := 49882825961979791003734937436160, coefficient := (-49882825961979791003734937436160) }, { argument := 186924700063455719855981854720, coefficient := (-186924700063455719855981854720) }, { argument := 191892226306880589127290454016, coefficient := (-191892226306880589127290454016) }, { argument := 5238878979742074364804705812480, coefficient := (-5238878979742074364804705812480) }, { argument := 3922146987799781170881320976384, coefficient := (-3922146987799781170881320976384) }, { argument := 49882831150989386120955919597568, coefficient := (-49882831150989386120955919597568) }, { argument := 5238878979742074364804705812480, coefficient := (-5238878979742074364804705812480) }, { argument := 186924700063455719855981854720, coefficient := (-186924700063455719855981854720) }, { argument := 184649237794878699352476352512, coefficient := (-184649237794878699352476352512) }, { argument := 170948350749110856535938957312, coefficient := (-170948350749110856535938957312) }, { argument := 184649237794878699352476352512, coefficient := (-184649237794878699352476352512) }, { argument := 3922146987799781170881320976384, coefficient := (-3922146987799781170881320976384) }, { argument := 170948350749110856535938957312, coefficient := (-170948350749110856535938957312) }, { argument := 790846408898129818470412451840, coefficient := (-790846408898129818470412451840) }, { argument := 191892226306880589127290454016, coefficient := (-191892226306880589127290454016) }, { argument := 38585376740402880859393228800, coefficient := (-38585376740402880859393228800) }, { argument := 5180045209708880174926358642688, coefficient := (-5180045209708880174926358642688) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 53686364038949446038948923047936, coefficient := (-53686364038949446038948923047936) }, { argument := 20595789168000904020558348288, coefficient := (-20595789168000904020558348288) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 26011021261237183580007825408, coefficient := (-26011021261237183580007825408) }, { argument := 20595789168000904020558348288, coefficient := (-20595789168000904020558348288) }, { argument := 406226956242230265086616797184, coefficient := (-406226956242230265086616797184) }, { argument := 26341284683583155087672868864, coefficient := (-26341284683583155087672868864) }, { argument := 5180046122201754381027412803584, coefficient := (-5180046122201754381027412803584) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 26341284683583155087672868864, coefficient := (-26341284683583155087672868864) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 30157107917469280248986075136, coefficient := (-30157107917469280248986075136) }, { argument := 26011021261237183580007825408, coefficient := (-26011021261237183580007825408) }, { argument := 38697862644286057489931173888, coefficient := (-38697862644286057489931173888) }, { argument := 1346356128999101589715156992, coefficient := (-1346356128999101589715156992) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1320657010599324980462223360, coefficient := (-1320657010599324980462223360) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 572041464940241175181296402432, coefficient := (-572041464940241175181296402432) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40372776656270005996804374528, coefficient := (-40372776656270005996804374528) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 1454734439780959947369480192, coefficient := (-1454734439780959947369480192) }, { argument := 21537456968359510360989892608, coefficient := (-21537456968359510360989892608) }, { argument := 790898019114886128088651923456, coefficient := (-790898019114886128088651923456) }, { argument := 790872356446225257464479088640, coefficient := (-790872356446225257464479088640) }, { argument := 21563143813784332590743814144, coefficient := (-21563143813784332590743814144) }, { argument := 129726750665975175590719782912, coefficient := (-129726750665975175590719782912) }, { argument := 191694522280417880824828919808, coefficient := (-191694522280417880824828919808) }, { argument := 1392655402424141553939024707584, coefficient := (-1392655402424141553939024707584) }, { argument := 227673117232478383265342816256, coefficient := (-227673117232478383265342816256) }, { argument := 8678925207674591643646820352, coefficient := (-8678925207674591643646820352) }, { argument := 227525975288799855074831499264, coefficient := (-227525975288799855074831499264) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
