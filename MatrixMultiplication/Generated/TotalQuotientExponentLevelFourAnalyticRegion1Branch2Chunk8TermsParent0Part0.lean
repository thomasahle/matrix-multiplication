import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8

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
def constantNumerator : ℤ := (-8405819015391423631123254138109952)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    480817, 7658959, 385, 341, 15961, 4345,
    7658961, 15961, 385, 385, 165, 385,
    4345, 165, 480815, 341, 52903810537111, 1233807885237677,
    118575, 7547086495119375, 121675, 3875, 118575, 67425,
    121675, 1899525, 2325, 1233808363388333, 118575, 3875,
    2325, 3875, 59675, 67425, 52903805289111, 496573782000705,
    6585801915, 7809701013914975, 162963566535, 5184567465, 15619408525633315, 2662345455,
    2662345455, 90099375135, 4904320575, 162963566535, 90099375135, 248285101229295,
    5184567465, 4904320575, 6585801915, 5576095, 890207915, 35531745185,
    890207915, 22301835, 180776925, 6792253475, 13583479525, 362581275,
    497347738932973, 366718905, 119666169, 1695420553904767
  ]
def negativeCoefficients : Array ℕ := #[
    18164752681551473621709357056, 289347290202182520289951219712, 14893966097652231432380088320, 13191798543634833554393792512, 617461280219811080239528804352, 168089045959218040451146711040,
    289347365760046246204274638848, 617461280219811080239528804352, 14893966097652231432380088320, 14893966097652231432380088320, 12766256655130484084897218560, 14893966097652231432380088320,
    168089045959218040451146711040, 12766256655130484084897218560, 18164677123687747707385937920, 13191798543634833554393792512, 59564395355353104861588619264, 2778288366101590914897748688896,
    1146787032486437235126278553600, 16994527963576259964284436480000, 1176768392812880038658991718400, 37476700408053504415891456000, 1146787032486437235126278553600, 652094587100130976836511334400,
    1176768392812880038658991718400, 18371078540027827864669991731200, 719552647834627284785115955200, 2778289442801149009176857411584, 1146787032486437235126278553600, 37476700408053504415891456000,
    719552647834627284785115955200, 37476700408053504415891456000, 1154282372568047936009456844800, 652094587100130976836511334400, 59564389446630393751497867264, 1118184749790166475836584099840,
    121486602446151266186444144640, 35171766576142466206565767577600, 3006147205210083459039032770560, 95638389159736103168051773440, 35171781207894872876943272837120, 98223210488377619469891010560,
    98223210488377619469891010560, 1662040114316494982082629468160, 90468746502453070564373299200, 3006147205210083459039032770560, 1662040114316494982082629468160, 1118176689377898840338013880320,
    95638389159736103168051773440, 90468746502453070564373299200, 121486602446151266186444144640, 51430398697845731109109760, 8210718790197793129832120320, 81930626239994580715039621120,
    8210718790197793129832120320, 51424530327387282258001920, 13338982679628744337077043200, 501179846148357432417871462400, 501141940856297570345733324800, 13376887971688606409215180800,
    1119927545866047964342390882304, 13529539575052012113321000960, 551862798456068915148619776, 3817747687400894294130704777216
  ]
def negativeScales : Array ℕ := #[
    18, 22, 8, 8, 13, 12,
    22, 13, 8, 8, 7, 8,
    12, 7, 18, 8, 45, 50,
    16, 52, 16, 11, 16, 16,
    16, 20, 11, 50, 16, 11,
    11, 11, 15, 16, 45, 48,
    32, 52, 37, 32, 53, 31,
    31, 36, 32, 37, 36, 47,
    32, 32, 32, 22, 29, 35,
    29, 24, 27, 32, 33, 28,
    48, 28, 26, 50
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18875128382793191, 22868716887229979, 8588714635586389, 8413627929024184, 13962263435507551, 12085140461701763,
    22868717263963923, 13962263435507551, 8588714635586389, 8588714635586389, 7366322214245818, 8588714635586389,
    12085140461701763, 7366322214245818, 18875122381765293, 8413627929024184, 45588436873554047, 50132039194951634,
    16855440344775225, 52744841232152023, 16892673252880949, 11919980601271074, 16855440344775225, 16040995996010329,
    16892673252880949, 20857207271014767, 11183015000882757, 50132039754054437, 16855440344775225, 11919980601271074,
    11183015000882757, 11919980601271074, 15864839043149652, 16040995996010329, 45588436730440274, 48819001421782825,
    32616711973801983, 52794188741265506, 37245758503588644, 32271576487744375, 53794189341438729, 31310050635559011,
    31310050635559011, 36390798049443377, 32191406139060392, 37245758503588644, 36390798049443377, 47818991022106976,
    32271576487744375, 32191406139060392, 32616711973801983, 22410823709953291, 29729567087352263, 35048389499009471,
    29729567087352263, 24410659084513403, 27429635297954808, 32661243152761510, 33661134034556853, 28433729180148478,
    48821248247214556, 28450099400514549, 26834440103853605, 50590564605688748
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
noncomputable def negativeCeiling : ℝ := 3772170513 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18164752681551473621709357056, coefficient := (-18164752681551473621709357056) }, { argument := 289347290202182520289951219712, coefficient := (-289347290202182520289951219712) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 13191798543634833554393792512, coefficient := (-13191798543634833554393792512) }, { argument := 617461280219811080239528804352, coefficient := (-617461280219811080239528804352) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 289347365760046246204274638848, coefficient := (-289347365760046246204274638848) }, { argument := 617461280219811080239528804352, coefficient := (-617461280219811080239528804352) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 12766256655130484084897218560, coefficient := (-12766256655130484084897218560) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 12766256655130484084897218560, coefficient := (-12766256655130484084897218560) }, { argument := 18164677123687747707385937920, coefficient := (-18164677123687747707385937920) }, { argument := 13191798543634833554393792512, coefficient := (-13191798543634833554393792512) }, { argument := 59564395355353104861588619264, coefficient := (-59564395355353104861588619264) }, { argument := 2778288366101590914897748688896, coefficient := (-2778288366101590914897748688896) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 16994527963576259964284436480000, coefficient := (-16994527963576259964284436480000) }, { argument := 1176768392812880038658991718400, coefficient := (-1176768392812880038658991718400) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 652094587100130976836511334400, coefficient := (-652094587100130976836511334400) }, { argument := 1176768392812880038658991718400, coefficient := (-1176768392812880038658991718400) }, { argument := 18371078540027827864669991731200, coefficient := (-18371078540027827864669991731200) }, { argument := 719552647834627284785115955200, coefficient := (-719552647834627284785115955200) }, { argument := 2778289442801149009176857411584, coefficient := (-2778289442801149009176857411584) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 719552647834627284785115955200, coefficient := (-719552647834627284785115955200) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 1154282372568047936009456844800, coefficient := (-1154282372568047936009456844800) }, { argument := 652094587100130976836511334400, coefficient := (-652094587100130976836511334400) }, { argument := 59564389446630393751497867264, coefficient := (-59564389446630393751497867264) }, { argument := 1118184749790166475836584099840, coefficient := (-1118184749790166475836584099840) }, { argument := 121486602446151266186444144640, coefficient := (-121486602446151266186444144640) }, { argument := 35171766576142466206565767577600, coefficient := (-35171766576142466206565767577600) }, { argument := 3006147205210083459039032770560, coefficient := (-3006147205210083459039032770560) }, { argument := 95638389159736103168051773440, coefficient := (-95638389159736103168051773440) }, { argument := 35171781207894872876943272837120, coefficient := (-35171781207894872876943272837120) }, { argument := 98223210488377619469891010560, coefficient := (-98223210488377619469891010560) }, { argument := 98223210488377619469891010560, coefficient := (-98223210488377619469891010560) }, { argument := 1662040114316494982082629468160, coefficient := (-1662040114316494982082629468160) }, { argument := 90468746502453070564373299200, coefficient := (-90468746502453070564373299200) }, { argument := 3006147205210083459039032770560, coefficient := (-3006147205210083459039032770560) }, { argument := 1662040114316494982082629468160, coefficient := (-1662040114316494982082629468160) }, { argument := 1118176689377898840338013880320, coefficient := (-1118176689377898840338013880320) }, { argument := 95638389159736103168051773440, coefficient := (-95638389159736103168051773440) }, { argument := 90468746502453070564373299200, coefficient := (-90468746502453070564373299200) }, { argument := 121486602446151266186444144640, coefficient := (-121486602446151266186444144640) }, { argument := 51430398697845731109109760, coefficient := (-51430398697845731109109760) }, { argument := 8210718790197793129832120320, coefficient := (-8210718790197793129832120320) }, { argument := 81930626239994580715039621120, coefficient := (-81930626239994580715039621120) }, { argument := 8210718790197793129832120320, coefficient := (-8210718790197793129832120320) }, { argument := 51424530327387282258001920, coefficient := (-51424530327387282258001920) }, { argument := 13338982679628744337077043200, coefficient := (-13338982679628744337077043200) }, { argument := 501179846148357432417871462400, coefficient := (-501179846148357432417871462400) }, { argument := 501141940856297570345733324800, coefficient := (-501141940856297570345733324800) }, { argument := 13376887971688606409215180800, coefficient := (-13376887971688606409215180800) }, { argument := 1119927545866047964342390882304, coefficient := (-1119927545866047964342390882304) }, { argument := 13529539575052012113321000960, coefficient := (-13529539575052012113321000960) }, { argument := 551862798456068915148619776, coefficient := (-551862798456068915148619776) }, { argument := 3817747687400894294130704777216, coefficient := (-3817747687400894294130704777216) }] }

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
def constantNumerator : ℤ := (-28049789738962504262278673864851456)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1208242287, 124336926532517, 2420344773, 1084715919, 366718905, 119666169,
    58990365, 2216419555, 4432503845, 118315995, 6549516505, 11241672487,
    6549516505, 104603579277149, 5576095, 104602695590051, 2815435, 52903377357161,
    1233775896031827, 118575, 7546753076976625, 121675, 3875, 118575,
    67425, 121675, 1899525, 2325, 1233776374182483, 118575,
    3875, 2325, 3875, 59675, 67425, 52903372109161,
    1692740673787875, 11303953221, 53210764337220127, 279712714809, 8898856791, 425686196968314947,
    4569683217, 4569683217, 154647700449, 8417837505, 279712714809, 154647700449,
    13541922256689069, 8898856791, 8417837505, 11303953221, 7828660594449491, 13778571335,
    4496165383, 53341886045429339, 45396766609, 15657320000110847, 90938570811, 40755563633,
    13778571335, 4496165383, 595612395, 22378687765
  ]
def negativeCoefficients : Array ℕ := #[
    11144068123661262609130192896, 1119927472000472597007500836864, 11161870149417909993489825792, 10004738475235830010113687552, 13529539575052012113321000960, 551862798456068915148619776,
    544090082984856676907089920, 20442862145525105795992125440, 20441316008612137737786490880, 545636219897824735112724480, 120817254774271644885141422080, 414744510656301932861387177984,
    120817254774271644885141422080, 58886580081773546716411199488, 51430398697845731109109760, 58886082610162888602038566912, 51935608901164451453992960, 59563907638087753769066430464,
    2778216332813817945852368388096, 1146787032486437235126278553600, 16993777172664536232863203328000, 1176768392812880038658991718400, 37476700408053504415891456000, 1146787032486437235126278553600,
    652094587100130976836511334400, 1176768392812880038658991718400, 18371078540027827864669991731200, 719552647834627284785115955200, 2778217409513376040131477110784, 1146787032486437235126278553600,
    37476700408053504415891456000, 719552647834627284785115955200, 37476700408053504415891456000, 1154282372568047936009456844800, 652094587100130976836511334400, 59563901729365042658975678464,
    3811713133852978087899168768000, 417042264177943494816297910272, 119819989220601920758987668586496, 10319577728488261371730946162688, 328309867544338495919213248512, 119820012377704172459981098975232,
    337183107207698995808921714688, 337183107207698995808921714688, 5705493103540801429082543751168, 310563388217617496139796316160, 10319577728488261371730946162688, 5705493103540801429082543751168,
    3811712251819069839486971019264, 328309867544338495919213248512, 310563388217617496139796316160, 417042264177943494816297910272, 35257152935972813373541015617536, 508339558236191110023841054720,
    20734903033318321593077727232, 120115249058717515793771970691072, 418711267705073203782795395072, 35257150259059912469307568685056, 419380135544857665769668870144, 375903725958867636622892990464,
    508339558236191110023841054720, 20734903033318321593077727232, 10987109417694202572381880320, 412813925906410200912615178240
  ]
def negativeScales : Array ℕ := #[
    30, 46, 31, 30, 28, 26,
    25, 31, 32, 26, 32, 33,
    32, 46, 22, 46, 21, 45,
    50, 16, 52, 16, 11, 16,
    16, 16, 20, 11, 50, 16,
    11, 11, 11, 15, 16, 45,
    50, 33, 55, 38, 33, 58,
    32, 32, 37, 32, 38, 37,
    53, 33, 32, 33, 52, 33,
    32, 55, 35, 53, 36, 35,
    33, 32, 29, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30170262639116172, 46821248152060628, 31172565424985593, 30014670112404480, 28450099400514549, 26834440103853605,
    25813976000867446, 31045583854789148, 32045474736584569, 26818069883134038, 32608741262691672, 33388137638276099,
    32608741262691672, 46571925546330224, 22410823709953291, 46571913358445373, 21424926413071481, 45588425060621898,
    50132001789398077, 16855440344775225, 52744777494797323, 16892673252880949, 11919980601271074, 16855440344775225,
    16040995996010329, 16892673252880949, 20857207271014767, 11183015000882757, 50132002348515376, 16855440344775225,
    11919980601271074, 11183015000882757, 11919980601271074, 15864839043149652, 16040995996010329, 45588424917506953,
    50588282394010078, 33396108349384680, 55562567645223654, 38025154879180256, 33050972863335987, 58562567924047193,
    32089447011150623, 32089447011150623, 37170194425034985, 32970802529400822, 38025154879180256, 37170194425034985,
    53588282060169086, 33050972863335987, 32970802529400822, 33396108349384680, 52797686921859426, 33681707255339724,
    32066047957348864, 55566118354342694, 35401870493894614, 53797686812322245, 36404173279764035, 35246277967182915,
    33681707255339724, 32066047957348864, 29149798536556457, 34381406391334894
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
noncomputable def negativeCeiling : ℝ := 166704072041 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11144068123661262609130192896, coefficient := (-11144068123661262609130192896) }, { argument := 1119927472000472597007500836864, coefficient := (-1119927472000472597007500836864) }, { argument := 11161870149417909993489825792, coefficient := (-11161870149417909993489825792) }, { argument := 10004738475235830010113687552, coefficient := (-10004738475235830010113687552) }, { argument := 13529539575052012113321000960, coefficient := (-13529539575052012113321000960) }, { argument := 551862798456068915148619776, coefficient := (-551862798456068915148619776) }, { argument := 544090082984856676907089920, coefficient := (-544090082984856676907089920) }, { argument := 20442862145525105795992125440, coefficient := (-20442862145525105795992125440) }, { argument := 20441316008612137737786490880, coefficient := (-20441316008612137737786490880) }, { argument := 545636219897824735112724480, coefficient := (-545636219897824735112724480) }, { argument := 120817254774271644885141422080, coefficient := (-120817254774271644885141422080) }, { argument := 414744510656301932861387177984, coefficient := (-414744510656301932861387177984) }, { argument := 120817254774271644885141422080, coefficient := (-120817254774271644885141422080) }, { argument := 58886580081773546716411199488, coefficient := (-58886580081773546716411199488) }, { argument := 51430398697845731109109760, coefficient := (-51430398697845731109109760) }, { argument := 58886082610162888602038566912, coefficient := (-58886082610162888602038566912) }, { argument := 51935608901164451453992960, coefficient := (-51935608901164451453992960) }, { argument := 59563907638087753769066430464, coefficient := (-59563907638087753769066430464) }, { argument := 2778216332813817945852368388096, coefficient := (-2778216332813817945852368388096) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 16993777172664536232863203328000, coefficient := (-16993777172664536232863203328000) }, { argument := 1176768392812880038658991718400, coefficient := (-1176768392812880038658991718400) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 652094587100130976836511334400, coefficient := (-652094587100130976836511334400) }, { argument := 1176768392812880038658991718400, coefficient := (-1176768392812880038658991718400) }, { argument := 18371078540027827864669991731200, coefficient := (-18371078540027827864669991731200) }, { argument := 719552647834627284785115955200, coefficient := (-719552647834627284785115955200) }, { argument := 2778217409513376040131477110784, coefficient := (-2778217409513376040131477110784) }, { argument := 1146787032486437235126278553600, coefficient := (-1146787032486437235126278553600) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 719552647834627284785115955200, coefficient := (-719552647834627284785115955200) }, { argument := 37476700408053504415891456000, coefficient := (-37476700408053504415891456000) }, { argument := 1154282372568047936009456844800, coefficient := (-1154282372568047936009456844800) }, { argument := 652094587100130976836511334400, coefficient := (-652094587100130976836511334400) }, { argument := 59563901729365042658975678464, coefficient := (-59563901729365042658975678464) }, { argument := 3811713133852978087899168768000, coefficient := (-3811713133852978087899168768000) }, { argument := 417042264177943494816297910272, coefficient := (-417042264177943494816297910272) }, { argument := 119819989220601920758987668586496, coefficient := (-119819989220601920758987668586496) }, { argument := 10319577728488261371730946162688, coefficient := (-10319577728488261371730946162688) }, { argument := 328309867544338495919213248512, coefficient := (-328309867544338495919213248512) }, { argument := 119820012377704172459981098975232, coefficient := (-119820012377704172459981098975232) }, { argument := 337183107207698995808921714688, coefficient := (-337183107207698995808921714688) }, { argument := 337183107207698995808921714688, coefficient := (-337183107207698995808921714688) }, { argument := 5705493103540801429082543751168, coefficient := (-5705493103540801429082543751168) }, { argument := 310563388217617496139796316160, coefficient := (-310563388217617496139796316160) }, { argument := 10319577728488261371730946162688, coefficient := (-10319577728488261371730946162688) }, { argument := 5705493103540801429082543751168, coefficient := (-5705493103540801429082543751168) }, { argument := 3811712251819069839486971019264, coefficient := (-3811712251819069839486971019264) }, { argument := 328309867544338495919213248512, coefficient := (-328309867544338495919213248512) }, { argument := 310563388217617496139796316160, coefficient := (-310563388217617496139796316160) }, { argument := 417042264177943494816297910272, coefficient := (-417042264177943494816297910272) }, { argument := 35257152935972813373541015617536, coefficient := (-35257152935972813373541015617536) }, { argument := 508339558236191110023841054720, coefficient := (-508339558236191110023841054720) }, { argument := 20734903033318321593077727232, coefficient := (-20734903033318321593077727232) }, { argument := 120115249058717515793771970691072, coefficient := (-120115249058717515793771970691072) }, { argument := 418711267705073203782795395072, coefficient := (-418711267705073203782795395072) }, { argument := 35257150259059912469307568685056, coefficient := (-35257150259059912469307568685056) }, { argument := 419380135544857665769668870144, coefficient := (-419380135544857665769668870144) }, { argument := 375903725958867636622892990464, coefficient := (-375903725958867636622892990464) }, { argument := 508339558236191110023841054720, coefficient := (-508339558236191110023841054720) }, { argument := 20734903033318321593077727232, coefficient := (-20734903033318321593077727232) }, { argument := 10987109417694202572381880320, coefficient := (-10987109417694202572381880320) }, { argument := 412813925906410200912615178240, coefficient := (-412813925906410200912615178240) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
