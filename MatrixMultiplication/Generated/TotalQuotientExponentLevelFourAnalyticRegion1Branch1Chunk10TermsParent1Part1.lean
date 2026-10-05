import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

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
def constantNumerator : ℤ := (-89382089201028086737596637436182528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    63172376631, 245670353565, 104323730840452725, 2048819961, 53162993, 189982865657702151,
    3300195027, 104331049675797373, 3300195027, 3439236701, 2048819961, 102236525,
    5245739679, 102306045837, 204612016623, 655720587, 775541899925, 2789601151025,
    387771079325, 3643660507543457, 24075, 3643661615368287, 24075, 68718902525,
    247179848825, 34359462725, 223001630661, 42265, 223001577531, 42265,
    13320593, 1350183115319271, 34149633945, 104194957652630693, 385403011665, 34149633945,
    52097483687453393, 34149633945, 34149633945, 1415746252977, 8781334443, 385403011665,
    1415746252977, 2700386120908267, 34149633945, 8781334443, 34149633945, 26080935153916499,
    4097638419, 106325947, 379965764983775347, 6600387633, 104331059458848321, 6600387633,
    6878470879, 4097638419, 204472975, 17546826998091089, 1605, 17546833111282351,
    1605, 68718902525, 247179848825, 34359462725
  ]
def negativeCoefficients : Array ℕ := #[
    291331166060011754997021671424, 283238633669455872913771069440, 117458078834740703450649486950400, 151176229894698338668882427904, 7845473008507299012756373504, 427803381491403204357706846568448,
    243511412225591934742092054528, 117466319110773439137766023626752, 243511412225591934742092054528, 253770876929024556528004235264, 151176229894698338668882427904, 7543724046641633666111897600,
    6047926083488518477084360704, 235901680593542186781401677824, 235901594065630344532929282048, 6047954926125799226575159296, 894138934147183743930780876800, 3216191156292735164345640550400,
    894139232436800023337264742400, 8204794052018652637446679822336, 454763892300346834078924800, 8204796546618398427338218930176, 454763892300346834078924800, 79227500494054255791335014400,
    284978963215811976587588403200, 79227526924779748903301939200, 1028413502205841997414786924544, 798363277593942219827445760, 1028413257186963838367667585024, 798363277593942219827445760,
    62904721915148015946042441728, 3040342087516902152502622814208, 78743694699284910742060400640, 117313093114568049898505143058432, 888678840177643992660395950080, 78743694699284910742060400640,
    117313104060877797305475571646464, 78743694699284910742060400640, 78743694699284910742060400640, 3264488600247497299620846895104, 80993514547835908191833554944, 888678840177643992660395950080,
    3264488600247497299620846895104, 3040364481969732604667109572608, 78743694699284910742060400640, 80993514547835908191833554944, 78743694699284910742060400640, 117458089840652414636331320213504,
    151176174443785653097970270208, 7845470130815223514066321408, 427803419398619027466106099990528, 243511322906457129840443129856, 117466330125509590127610433634304, 243511322906457129840443129856,
    253770783846753960589606780928, 151176174443785653097970270208, 7543721279630022609679155200, 79023883530137587347908559110144, 30317592820023122271928320, 79023911061503476935680742916096,
    30317592820023122271928320, 79227500494054255791335014400, 284978963215811976587588403200, 79227526924779748903301939200
  ]
def negativeScales : Array ℕ := #[
    35, 37, 56, 30, 25, 57,
    31, 56, 31, 31, 30, 26,
    32, 36, 37, 29, 39, 41,
    38, 51, 14, 51, 14, 35,
    37, 34, 37, 15, 37, 15,
    23, 50, 34, 56, 38, 34,
    55, 34, 34, 40, 33, 38,
    40, 51, 34, 33, 34, 54,
    31, 26, 58, 32, 56, 32,
    32, 31, 27, 53, 10, 53,
    10, 35, 37, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35878574801228164, 37837932815144707, 56533844982560294, 30932146075507131, 25663918992796928, 57398646922455356,
    31619904137913093, 56533946191336199, 31619904137913093, 31679441264925027, 30932146075507131, 26607335464407238,
    32288499069302788, 36574100448292966, 37574099919117371, 29288505949517588, 39496413771097459, 41343196003150094,
    38496414252388298, 51694309967886842, 14555248177619742, 51694310406526266, 14555248177619742, 35999987968649564,
    37846770178658948, 34999988449940585, 37698263303473527, 15367175829465614, 37698262959752288, 15367175829465614,
    23667154973313856, 50262076505881250, 34991151083555762, 56532063075485822, 38487576889129059, 34991151083555762,
    55532063210101538, 34991151083555762, 34991151083555762, 40364699850131162, 33031793047506728, 38487576889129059,
    40364699850131162, 51262087132398308, 34991151083555762, 33031793047506728, 34991151083555762, 54533845117741915,
    31932145546331466, 26663918463621333, 58398647050291068, 32619903608737498, 56533946326616717, 32619903608737498,
    32679440735749431, 31932145546331466, 27607334935231643, 53962059701773523, 10648357582030099, 53962060204398360,
    10648357582030099, 35999987968649564, 37846770178658948, 34999988449940585
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
noncomputable def negativeCeiling : ℝ := 299340580439 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 291331166060011754997021671424, coefficient := (-291331166060011754997021671424) }, { argument := 283238633669455872913771069440, coefficient := (-283238633669455872913771069440) }, { argument := 117458078834740703450649486950400, coefficient := (-117458078834740703450649486950400) }, { argument := 151176229894698338668882427904, coefficient := (-151176229894698338668882427904) }, { argument := 7845473008507299012756373504, coefficient := (-7845473008507299012756373504) }, { argument := 427803381491403204357706846568448, coefficient := (-427803381491403204357706846568448) }, { argument := 243511412225591934742092054528, coefficient := (-243511412225591934742092054528) }, { argument := 117466319110773439137766023626752, coefficient := (-117466319110773439137766023626752) }, { argument := 243511412225591934742092054528, coefficient := (-243511412225591934742092054528) }, { argument := 253770876929024556528004235264, coefficient := (-253770876929024556528004235264) }, { argument := 151176229894698338668882427904, coefficient := (-151176229894698338668882427904) }, { argument := 7543724046641633666111897600, coefficient := (-7543724046641633666111897600) }, { argument := 6047926083488518477084360704, coefficient := (-6047926083488518477084360704) }, { argument := 235901680593542186781401677824, coefficient := (-235901680593542186781401677824) }, { argument := 235901594065630344532929282048, coefficient := (-235901594065630344532929282048) }, { argument := 6047954926125799226575159296, coefficient := (-6047954926125799226575159296) }, { argument := 894138934147183743930780876800, coefficient := (-894138934147183743930780876800) }, { argument := 3216191156292735164345640550400, coefficient := (-3216191156292735164345640550400) }, { argument := 894139232436800023337264742400, coefficient := (-894139232436800023337264742400) }, { argument := 8204794052018652637446679822336, coefficient := (-8204794052018652637446679822336) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 8204796546618398427338218930176, coefficient := (-8204796546618398427338218930176) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }, { argument := 1028413502205841997414786924544, coefficient := (-1028413502205841997414786924544) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1028413257186963838367667585024, coefficient := (-1028413257186963838367667585024) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 62904721915148015946042441728, coefficient := (-62904721915148015946042441728) }, { argument := 3040342087516902152502622814208, coefficient := (-3040342087516902152502622814208) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 117313093114568049898505143058432, coefficient := (-117313093114568049898505143058432) }, { argument := 888678840177643992660395950080, coefficient := (-888678840177643992660395950080) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 117313104060877797305475571646464, coefficient := (-117313104060877797305475571646464) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 3264488600247497299620846895104, coefficient := (-3264488600247497299620846895104) }, { argument := 80993514547835908191833554944, coefficient := (-80993514547835908191833554944) }, { argument := 888678840177643992660395950080, coefficient := (-888678840177643992660395950080) }, { argument := 3264488600247497299620846895104, coefficient := (-3264488600247497299620846895104) }, { argument := 3040364481969732604667109572608, coefficient := (-3040364481969732604667109572608) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 80993514547835908191833554944, coefficient := (-80993514547835908191833554944) }, { argument := 78743694699284910742060400640, coefficient := (-78743694699284910742060400640) }, { argument := 117458089840652414636331320213504, coefficient := (-117458089840652414636331320213504) }, { argument := 151176174443785653097970270208, coefficient := (-151176174443785653097970270208) }, { argument := 7845470130815223514066321408, coefficient := (-7845470130815223514066321408) }, { argument := 427803419398619027466106099990528, coefficient := (-427803419398619027466106099990528) }, { argument := 243511322906457129840443129856, coefficient := (-243511322906457129840443129856) }, { argument := 117466330125509590127610433634304, coefficient := (-117466330125509590127610433634304) }, { argument := 243511322906457129840443129856, coefficient := (-243511322906457129840443129856) }, { argument := 253770783846753960589606780928, coefficient := (-253770783846753960589606780928) }, { argument := 151176174443785653097970270208, coefficient := (-151176174443785653097970270208) }, { argument := 7543721279630022609679155200, coefficient := (-7543721279630022609679155200) }, { argument := 79023883530137587347908559110144, coefficient := (-79023883530137587347908559110144) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 79023911061503476935680742916096, coefficient := (-79023911061503476935680742916096) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }] }

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
def constantNumerator : ℤ := (-2105999352144742776365609769762816)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8688469515, 13375, 8688467445, 13375, 467197551, 14482368189,
    1605, 14482364739, 1605, 2109, 1605, 24075,
    42265, 1605, 13375, 1605, 42265, 83995,
    13375, 1296305, 82925, 24075, 42265, 1605,
    82925, 1605, 42265, 42265, 1605, 5245739679,
    102306045837, 204612016623, 655720587, 68718902525, 247179848825, 34359462725,
    5466749777, 106616337731, 213232597249, 683346981, 2848889358965, 10247370304145,
    1424445154685, 443109191217, 42265, 443109085647, 42265, 17670574935,
    63560532555, 8835290415, 14480177469, 83995, 14480174019, 83995,
    171, 3256648797, 63513418791, 127026790989, 407083041, 775541899925,
    2789601151025, 387771079325, 8688469515, 13375
  ]
def negativeCoefficients : Array ℕ := #[
    641095894141729408719739944960, 505293213667052037865472000, 641095741402688478404652564480, 505293213667052037865472000, 2206278055721181696077642858496, 33394067445464435193626492928,
    30317592820023122271928320, 33394059490306053406382358528, 30317592820023122271928320, 40793992857076046871285202944, 30317592820023122271928320, 454763892300346834078924800,
    798363277593942219827445760, 30317592820023122271928320, 505293213667052037865472000, 30317592820023122271928320, 798363277593942219827445760, 793310345457271699448791040,
    505293213667052037865472000, 12243254567152670877480386560, 783204481183930658691481600, 454763892300346834078924800, 798363277593942219827445760, 30317592820023122271928320,
    783204481183930658691481600, 30317592820023122271928320, 798363277593942219827445760, 798363277593942219827445760, 30317592820023122271928320, 6047926083488518477084360704,
    235901680593542186781401677824, 235901594065630344532929282048, 6047954926125799226575159296, 79227500494054255791335014400, 284978963215811976587588403200, 79227526924779748903301939200,
    6302733378207985178721124352, 245840537024992539136504102912, 245840446851542899321181569024, 6302763436024531783828635648, 3284545806196363575806488739840, 11814413589318376515102593515520,
    3284546901938726161676888965120, 1021740230886053406191684419584, 798363277593942219827445760, 1021739987458206923502013906944, 798363277593942219827445760, 81491143365312948813944586240,
    293121219307692318775805214720, 81491170551202027443396280320, 1068448511650153298240382959616, 793310345457271699448791040, 1068448257085085081048570658816, 793310345457271699448791040,
    52921936679450006751937560576, 3754660431013318162353487872, 146451972710489015585479852032, 146451918992417351438658699264, 3754678337037206211293872128, 894138934147183743930780876800,
    3216191156292735164345640550400, 894139232436800023337264742400, 641095894141729408719739944960, 505293213667052037865472000
  ]
def negativeScales : Array ℕ := #[
    33, 13, 33, 13, 28, 33,
    10, 33, 10, 11, 10, 14,
    15, 10, 13, 10, 15, 16,
    13, 20, 16, 14, 15, 10,
    16, 10, 15, 15, 10, 32,
    36, 37, 29, 35, 37, 34,
    32, 36, 37, 29, 41, 43,
    40, 38, 15, 38, 15, 34,
    35, 33, 33, 16, 33, 16,
    7, 31, 35, 36, 28, 39,
    41, 38, 33, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33016454920832464, 13707251271149006, 33016454577114956, 13707251271149006, 28799457471521218, 33753578483524610,
    10648357582030099, 33753578139844733, 10648357582030099, 11042343379793692, 10648357582030099, 14555248177619742,
    15367175829465614, 10648357582030099, 13707251271149006, 10648357582030099, 15367175829465614, 16358015830180138,
    13707251271149006, 20305973770739856, 16339519486562748, 14555248177619742, 15367175829465614, 10648357582030099,
    16339519486562748, 10648357582030099, 15367175829465614, 15367175829465614, 10648357582030099, 32288499069302788,
    36574100448292966, 37574099919117371, 29288505949517588, 35999987968649564, 37846770178658948, 34999988449940585,
    32348036196280152, 36633637575281586, 37633637046105991, 29348043076494952, 41373536732099500, 43220318964152373,
    40373537213390339, 38688871296132785, 15367175829465614, 38688870952413140, 15367175829465614, 34040629929475065,
    35887412165007083, 33040630410765905, 33753360233310005, 16358015830180138, 33753359889578133, 16358015830180138,
    7417852514885912, 31600740999225987, 35886342381619663, 36886341852444035, 28600747879440788, 39496413771097459,
    41343196003150094, 38496414252388298, 33016454920832464, 13707251271149006
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
noncomputable def negativeCeiling : ℝ := 16170516749 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 641095894141729408719739944960, coefficient := (-641095894141729408719739944960) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 641095741402688478404652564480, coefficient := (-641095741402688478404652564480) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 2206278055721181696077642858496, coefficient := (-2206278055721181696077642858496) }, { argument := 33394067445464435193626492928, coefficient := (-33394067445464435193626492928) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 33394059490306053406382358528, coefficient := (-33394059490306053406382358528) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 40793992857076046871285202944, coefficient := (-40793992857076046871285202944) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 793310345457271699448791040, coefficient := (-793310345457271699448791040) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 12243254567152670877480386560, coefficient := (-12243254567152670877480386560) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 6047926083488518477084360704, coefficient := (-6047926083488518477084360704) }, { argument := 235901680593542186781401677824, coefficient := (-235901680593542186781401677824) }, { argument := 235901594065630344532929282048, coefficient := (-235901594065630344532929282048) }, { argument := 6047954926125799226575159296, coefficient := (-6047954926125799226575159296) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }, { argument := 6302733378207985178721124352, coefficient := (-6302733378207985178721124352) }, { argument := 245840537024992539136504102912, coefficient := (-245840537024992539136504102912) }, { argument := 245840446851542899321181569024, coefficient := (-245840446851542899321181569024) }, { argument := 6302763436024531783828635648, coefficient := (-6302763436024531783828635648) }, { argument := 3284545806196363575806488739840, coefficient := (-3284545806196363575806488739840) }, { argument := 11814413589318376515102593515520, coefficient := (-11814413589318376515102593515520) }, { argument := 3284546901938726161676888965120, coefficient := (-3284546901938726161676888965120) }, { argument := 1021740230886053406191684419584, coefficient := (-1021740230886053406191684419584) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1021739987458206923502013906944, coefficient := (-1021739987458206923502013906944) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 81491143365312948813944586240, coefficient := (-81491143365312948813944586240) }, { argument := 293121219307692318775805214720, coefficient := (-293121219307692318775805214720) }, { argument := 81491170551202027443396280320, coefficient := (-81491170551202027443396280320) }, { argument := 1068448511650153298240382959616, coefficient := (-1068448511650153298240382959616) }, { argument := 793310345457271699448791040, coefficient := (-793310345457271699448791040) }, { argument := 1068448257085085081048570658816, coefficient := (-1068448257085085081048570658816) }, { argument := 793310345457271699448791040, coefficient := (-793310345457271699448791040) }, { argument := 52921936679450006751937560576, coefficient := (-52921936679450006751937560576) }, { argument := 3754660431013318162353487872, coefficient := (-3754660431013318162353487872) }, { argument := 146451972710489015585479852032, coefficient := (-146451972710489015585479852032) }, { argument := 146451918992417351438658699264, coefficient := (-146451918992417351438658699264) }, { argument := 3754678337037206211293872128, coefficient := (-3754678337037206211293872128) }, { argument := 894138934147183743930780876800, coefficient := (-894138934147183743930780876800) }, { argument := 3216191156292735164345640550400, coefficient := (-3216191156292735164345640550400) }, { argument := 894139232436800023337264742400, coefficient := (-894139232436800023337264742400) }, { argument := 641095894141729408719739944960, coefficient := (-641095894141729408719739944960) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
