import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
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

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 128234765348164239789631169592557568
def positiveArguments : Array ℕ := #[
    16907, 1017, 29493, 26103, 1695, 1017,
    1695, 51867, 1695
  ]
def positiveCoefficients : Array ℕ := #[
    1339510543628667155694047568330752, 39343281873538491861637791744, 570477587166308131993747980288, 1009810901420821291115369988096, 32786068227948743218031493120, 629492509976615869786204667904,
    32786068227948743218031493120, 1003253687775231542471763689472, 1049154183294359782977007779840
  ]
def positiveScales : Array ℕ := #[
    14, 9, 14, 14, 10, 9,
    10, 15, 10
  ]
def negativeArguments : Array ℕ := #[
    1201026528779, 237991577, 80341278985, 288482209417, 40176457783, 974988221,
    19221542735, 38443073445, 1904279, 161974226365, 581612098333, 80998731667,
    85941288965, 85941288955, 26089213473, 13580614198581, 79305, 536096944914339,
    12453, 5583, 158091, 80613, 12453, 2478723,
    158673, 54322512602985, 158091, 5583, 158673, 5583,
    158091, 40431, 26089213473, 20711843499253, 813628466578907, 813628414145291,
    20711944452645, 1882934082817, 6931879243855, 117669817643, 159539105, 196603163,
    1572824813, 159539531, 96358418357, 346002561839, 24093050695, 42823843825,
    42823843855, 7907137543, 28392551095, 3954137761, 85941288965, 85941288955,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    5538757250530493122805252489216, 140485430803761293729751629824, 185254376498849311280039198720, 665194685866710319165010345984, 185281208627799310176020856832, 4496339546917092150197878784,
    177287439767208068182316154880, 177287384311683696592976609280, 4496351661816262558945902592, 186743568768265822419539722240, 670553095507627795910395691008, 186770359169527805079908777984,
    99083560181379614681952419840, 99083560169850399635883950080, 234990744150784247611785216, 30580824522095929383702233088, 1498029095695908854688645120, 301795750168834805131816992768,
    940922076978811069538500608, 52729944147722458456129536, 1493127279286690162956828672, 1522736517134282838446702592, 940922076978811069538500608, 23410876831036191186056380416,
    1498624113872750429985570816, 30580855939579039839493816320, 1493127279286690162956828672, 52729944147722458456129536, 1498624113872750429985570816, 52729944147722458456129536,
    1493127279286690162956828672, 1527439994151221005079543808, 234990744150784247611785216, 11659731333173980093466279936, 458032107362849202952663465984, 458032077845347518041703841792,
    11659788164881304216917770240, 33919924934951391420825468928, 124873635118410614297665208320, 33916015800945217018781499392, 5885954079367351789535887360, 232108046844339391425111130112,
    232107974385528669893992382464, 5885969795993302590073864192, 222187385347376927440176676864, 797827588386486988392500297728, 222219170062787521895003586560, 98745060911535265851795046400,
    98745060980710556128205864960, 9116308913208847178785619968, 32734382728074180652926238720, 9117620913669738173900521472, 99083560181379614681952419840, 99083560169850399635883950080,
    79228162514264337593543950336
  ]
def negativeScales : Array ℕ := #[
    40, 27, 36, 38, 35, 29,
    34, 35, 20, 37, 39, 36,
    36, 36, 34, 43, 16, 48,
    13, 12, 17, 16, 13, 21,
    17, 45, 17, 12, 17, 12,
    17, 15, 34, 44, 49, 49,
    44, 40, 42, 36, 27, 27,
    30, 27, 36, 38, 34, 35,
    35, 32, 34, 31, 36, 36,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14045333068328068, 9990103962611722, 14848084958881724, 14671928003828954, 10727069558015321, 9990103962611722,
    10727069558015321, 15662529305827180, 10727069558015321
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40127405156898562, 27826335274754877, 36225422377280027, 38069691394946232, 35225631321203332, 29860809550746122,
    34162005081385575, 35162004630110388, 20860813437926332, 37236973310861034, 39081266323375242, 36237180266351683,
    36322632363982545, 36322632363814675, 34602734399907192, 43626613962114446, 16275124206989461, 48929487249321402,
    13604205717331114, 12446824840780350, 17270395712943008, 16298724892287697, 13604205717331114, 21241165627011478,
    17275697132666352, 45626615444279317, 17270395712943008, 12446824840780350, 17275697132666352, 12446824840780350,
    17270395712943008, 15303174266493198, 34602734399907192, 44235521202780511, 49531363484356912, 49531363391383616,
    44235528234728346, 40776119634449684, 42656383661058234, 36775953360104944, 27249334848761824, 27550711291397810,
    30550710841021424, 27249338701029059, 36487691662009759, 38331991763526854, 34487898030033898, 35317695245259829,
    35317695246270501, 32880508377298916, 34724793431271525, 31880715992079339, 36322632363982545, 36322632363814675,
    0
  ]

abbrev PositiveTerm := Fin 9
abbrev NegativeTerm := Fin 55
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
noncomputable def positiveFloor : ℝ := 227157551809 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2846957631 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5538757250530493122805252489216, coefficient := (-5538757250530493122805252489216) }, { argument := 140485430803761293729751629824, coefficient := (-140485430803761293729751629824) }, { argument := 185254376498849311280039198720, coefficient := (-185254376498849311280039198720) }, { argument := 665194685866710319165010345984, coefficient := (-665194685866710319165010345984) }, { argument := 185281208627799310176020856832, coefficient := (-185281208627799310176020856832) }, { argument := 4496339546917092150197878784, coefficient := (-4496339546917092150197878784) }, { argument := 177287439767208068182316154880, coefficient := (-177287439767208068182316154880) }, { argument := 177287384311683696592976609280, coefficient := (-177287384311683696592976609280) }, { argument := 4496351661816262558945902592, coefficient := (-4496351661816262558945902592) }, { argument := 186743568768265822419539722240, coefficient := (-186743568768265822419539722240) }, { argument := 670553095507627795910395691008, coefficient := (-670553095507627795910395691008) }, { argument := 186770359169527805079908777984, coefficient := (-186770359169527805079908777984) }, { argument := 99083560181379614681952419840, coefficient := (-99083560181379614681952419840) }, { argument := 99083560169850399635883950080, coefficient := (-99083560169850399635883950080) }, { argument := 234990744150784247611785216, coefficient := (-234990744150784247611785216) }, { argument := 30580824522095929383702233088, coefficient := (-30580824522095929383702233088) }, { argument := 1498029095695908854688645120, coefficient := (-1498029095695908854688645120) }, { argument := 301795750168834805131816992768, coefficient := (-301795750168834805131816992768) }, { argument := 940922076978811069538500608, coefficient := (-940922076978811069538500608) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 1522736517134282838446702592, coefficient := (-1522736517134282838446702592) }, { argument := 940922076978811069538500608, coefficient := (-940922076978811069538500608) }, { argument := 23410876831036191186056380416, coefficient := (-23410876831036191186056380416) }, { argument := 1498624113872750429985570816, coefficient := (-1498624113872750429985570816) }, { argument := 30580855939579039839493816320, coefficient := (-30580855939579039839493816320) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1498624113872750429985570816, coefficient := (-1498624113872750429985570816) }, { argument := 52729944147722458456129536, coefficient := (-52729944147722458456129536) }, { argument := 1493127279286690162956828672, coefficient := (-1493127279286690162956828672) }, { argument := 1527439994151221005079543808, coefficient := (-1527439994151221005079543808) }, { argument := 234990744150784247611785216, coefficient := (-234990744150784247611785216) }, { argument := 11659731333173980093466279936, coefficient := (-11659731333173980093466279936) }, { argument := 458032107362849202952663465984, coefficient := (-458032107362849202952663465984) }, { argument := 458032077845347518041703841792, coefficient := (-458032077845347518041703841792) }, { argument := 11659788164881304216917770240, coefficient := (-11659788164881304216917770240) }, { argument := 33919924934951391420825468928, coefficient := (-33919924934951391420825468928) }, { argument := 124873635118410614297665208320, coefficient := (-124873635118410614297665208320) }, { argument := 33916015800945217018781499392, coefficient := (-33916015800945217018781499392) }, { argument := 5885954079367351789535887360, coefficient := (-5885954079367351789535887360) }, { argument := 232108046844339391425111130112, coefficient := (-232108046844339391425111130112) }, { argument := 232107974385528669893992382464, coefficient := (-232107974385528669893992382464) }, { argument := 5885969795993302590073864192, coefficient := (-5885969795993302590073864192) }, { argument := 222187385347376927440176676864, coefficient := (-222187385347376927440176676864) }, { argument := 797827588386486988392500297728, coefficient := (-797827588386486988392500297728) }, { argument := 222219170062787521895003586560, coefficient := (-222219170062787521895003586560) }, { argument := 98745060911535265851795046400, coefficient := (-98745060911535265851795046400) }, { argument := 98745060980710556128205864960, coefficient := (-98745060980710556128205864960) }, { argument := 9116308913208847178785619968, coefficient := (-9116308913208847178785619968) }, { argument := 32734382728074180652926238720, coefficient := (-32734382728074180652926238720) }, { argument := 9117620913669738173900521472, coefficient := (-9117620913669738173900521472) }, { argument := 99083560181379614681952419840, coefficient := (-99083560181379614681952419840) }, { argument := 99083560169850399635883950080, coefficient := (-99083560169850399635883950080) }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1339510543628667155694047568330752, coefficient := 1339510543628667155694047568330752 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 570477587166308131993747980288, coefficient := 570477587166308131993747980288 }, { argument := 1009810901420821291115369988096, coefficient := 1009810901420821291115369988096 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 629492509976615869786204667904, coefficient := 629492509976615869786204667904 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 1049154183294359782977007779840, coefficient := 1049154183294359782977007779840 }] }

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


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1332417882230460252413413807882240)
def positiveArguments : Array ℕ := #[
    1017, 830889, 53223, 29493, 51867, 1695,
    53223, 1695, 51867, 1695, 1017, 13207,
    9835, 10397, 843, 180683, 326803, 9835,
    180683, 5339, 5339, 10397, 10397, 326803,
    10397, 13207, 843, 1333, 4085, 12083,
    26961, 1333, 13459, 27391, 1333, 4085,
    1333, 1285, 5125, 2545, 5125, 1,
    5, 5, 5, 5, 2573, 62333,
    47227, 26311, 2573, 26311, 52539, 2573,
    62333, 2573, 1365
  ]
def positiveCoefficients : Array ℕ := #[
    629492509976615869786204667904, 16071730645340473925479037927424, 1029482542357590537046188883968, 570477587166308131993747980288, 1003253687775231542471763689472, 32786068227948743218031493120,
    1029482542357590537046188883968, 32786068227948743218031493120, 1003253687775231542471763689472, 1049154183294359782977007779840, 39343281873538491861637791744, 510921065588813040331022925824,
    380473133949116093863527710720, 402214455889065584941443579904, 521791726558787785869980860416, 6989835003693761381549951942656, 12642578708080629061808077930496, 380473133949116093863527710720,
    6989835003693761381549951942656, 413085116859040330480401514496, 413085116859040330480401514496, 402214455889065584941443579904, 402214455889065584941443579904, 12642578708080629061808077930496,
    402214455889065584941443579904, 510921065588813040331022925824, 521791726558787785869980860416, 51567939761481622076266643456, 1264246265120194605740730613760, 934876843417828116350382374912,
    1043003168724160549736102756352, 51567939761481622076266643456, 1041339686796370819991707058176, 1059637988002057847180059738112, 51567939761481622076266643456, 1264246265120194605740730613760,
    51567939761481622076266643456, 198844118810214206655671828480, 198263834416799184651812864000, 196909837498830799976141946880, 198263834416799184651812864000, 158456325028528675187087900672,
    198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 49769058141895053864303853568, 1205695569824618885551361097728,
    913503034927041472541577183232, 1017857511676176262902214295552, 49769058141895053864303853568, 1017857511676176262902214295552, 1016252058187728035358204493824, 49769058141895053864303853568,
    1205695569824618885551361097728, 49769058141895053864303853568, 422447038406136018809326141440
  ]
def positiveScales : Array ℕ := #[
    9, 19, 15, 14, 15, 10,
    15, 10, 15, 10, 9, 13,
    13, 13, 9, 17, 18, 13,
    17, 12, 12, 13, 13, 18,
    13, 13, 9, 10, 11, 13,
    14, 10, 13, 14, 10, 11,
    10, 10, 12, 11, 12, 0,
    2, 2, 2, 2, 11, 15,
    15, 14, 11, 14, 15, 11,
    15, 11, 10
  ]
def negativeArguments : Array ℕ := #[
    339, 281, 43, 5, 1, 5,
    83
  ]
def negativeCoefficients : Array ℕ := #[
    26858347092335610444211399163904, 44526227333016557727571700088832, 6813621976226733033044779728896, 792281625142643375935439503360, 158456325028528675187087900672, 792281625142643375935439503360,
    6575937488683940020264147877888
  ]
def negativeScales : Array ℕ := #[
    8, 8, 5, 2, 0, 2,
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9990103962611722, 19664296232001286, 15699762212023501, 14848084958881724, 15662529305827180, 10727069558015321,
    15699762212023501, 10727069558015321, 15662529305827180, 10727069558015321, 9990103962611722, 13689015171895098,
    13263709337165892, 13343879685849875, 9719388820935039, 17463101247548868, 18318061701694144, 13263709337165892,
    17463101247548868, 12382353833664511, 12382353833664511, 13343879685849875, 13343879685849875, 18318061701694144,
    13343879685849875, 13689015171895098, 9719388820935039, 10380461065088972, 11996120361661050, 13560691074922909,
    14718586387497221, 10380461065088972, 13716283601628156, 14741414316946847, 10380461065088972, 11996120361661050,
    10380461065088972, 10327552644081240, 12323336289280170, 11313449940963057, 12323336289280170, 0,
    2321928094887362, 2321928094887362, 2321928094887362, 2321928094887362, 11329235741733799, 15927708528421497,
    15527324273653465, 14683378461483305, 11329235741733799, 14683378461483305, 15681101120772401, 11329235741733799,
    15927708528421497, 11329235741733799, 10414685235807213
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8405141463136353, 8134426320220927, 5426264754702117, 2321928094887363, 0, 2321928094887363,
    6375039431346928
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 8345387749 / 500000000000
noncomputable def negativeCeiling : ℝ := 8071056511 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 629492509976615869786204667904, coefficient := 629492509976615869786204667904 }, { argument := 16071730645340473925479037927424, coefficient := 16071730645340473925479037927424 }, { argument := 1029482542357590537046188883968, coefficient := 1029482542357590537046188883968 }, { argument := 570477587166308131993747980288, coefficient := 570477587166308131993747980288 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 1029482542357590537046188883968, coefficient := 1029482542357590537046188883968 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 1049154183294359782977007779840, coefficient := 1049154183294359782977007779840 }, { argument := 39343281873538491861637791744, coefficient := 39343281873538491861637791744 }, { argument := 26858347092335610444211399163904, coefficient := (-26858347092335610444211399163904) }, { argument := 510921065588813040331022925824, coefficient := 510921065588813040331022925824 }, { argument := 380473133949116093863527710720, coefficient := 380473133949116093863527710720 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 521791726558787785869980860416, coefficient := 521791726558787785869980860416 }, { argument := 6989835003693761381549951942656, coefficient := 6989835003693761381549951942656 }, { argument := 12642578708080629061808077930496, coefficient := 12642578708080629061808077930496 }, { argument := 380473133949116093863527710720, coefficient := 380473133949116093863527710720 }, { argument := 6989835003693761381549951942656, coefficient := 6989835003693761381549951942656 }, { argument := 413085116859040330480401514496, coefficient := 413085116859040330480401514496 }, { argument := 413085116859040330480401514496, coefficient := 413085116859040330480401514496 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 12642578708080629061808077930496, coefficient := 12642578708080629061808077930496 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 510921065588813040331022925824, coefficient := 510921065588813040331022925824 }, { argument := 521791726558787785869980860416, coefficient := 521791726558787785869980860416 }, { argument := 44526227333016557727571700088832, coefficient := (-44526227333016557727571700088832) }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1264246265120194605740730613760, coefficient := 1264246265120194605740730613760 }, { argument := 934876843417828116350382374912, coefficient := 934876843417828116350382374912 }, { argument := 1043003168724160549736102756352, coefficient := 1043003168724160549736102756352 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1041339686796370819991707058176, coefficient := 1041339686796370819991707058176 }, { argument := 1059637988002057847180059738112, coefficient := 1059637988002057847180059738112 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1264246265120194605740730613760, coefficient := 1264246265120194605740730613760 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 6813621976226733033044779728896, coefficient := (-6813621976226733033044779728896) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 49769058141895053864303853568, coefficient := 49769058141895053864303853568 }, { argument := 1205695569824618885551361097728, coefficient := 1205695569824618885551361097728 }, { argument := 913503034927041472541577183232, coefficient := 913503034927041472541577183232 }, { argument := 1017857511676176262902214295552, coefficient := 1017857511676176262902214295552 }, { argument := 49769058141895053864303853568, coefficient := 49769058141895053864303853568 }, { argument := 1017857511676176262902214295552, coefficient := 1017857511676176262902214295552 }, { argument := 1016252058187728035358204493824, coefficient := 1016252058187728035358204493824 }, { argument := 49769058141895053864303853568, coefficient := 49769058141895053864303853568 }, { argument := 1205695569824618885551361097728, coefficient := 1205695569824618885551361097728 }, { argument := 49769058141895053864303853568, coefficient := 49769058141895053864303853568 }, { argument := 6575937488683940020264147877888, coefficient := (-6575937488683940020264147877888) }, { argument := 422447038406136018809326141440, coefficient := 422447038406136018809326141440 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
