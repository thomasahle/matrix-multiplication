import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17238578134774625477810153796403200)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    44753990435, 1194609885, 162065695645, 278171597923, 162065695645, 2441580901519375,
    890207915, 2441515643539441, 449476295, 5156002355, 8849827277, 5156002355,
    58599, 58599, 498737, 124143437327607, 6585801915, 15619400843123491,
    162963566535, 5184567465, 124955258727411365, 2662345455, 2662345455, 90099375135,
    4904320575, 162963566535, 90099375135, 3972561358149987, 5184567465, 4904320575,
    6585801915, 15657327693988639, 27555058465, 8991650657, 426735169486207215, 90786666311,
    125258612041600537, 181863385869, 81504962407, 27555058465, 8991650657, 14945479607063685,
    35531745185, 14944799434052475, 17940390005, 2647676885, 4544505899, 2647676885,
    60131, 60131, 7677391, 1915, 1915, 805,
    2815435, 449476295, 17940390005, 449476295, 11260455, 1193127705,
    44828872935, 89650964865, 2393036415, 2647676885
  ]
def negativeCoefficients : Array ℕ := #[
    412782703915845103995301396480, 11018331408259299489695662080, 2989584410691019638328073912320, 10262720550920832934421133787136, 2989584410691019638328073912320, 2748975709569394235240611840000,
    8210718790197793129832120320, 2748902235615865806814323933184, 8291374181064176166470942720, 95111455886128741718090055680, 326500997750705776933432459264, 95111455886128741718090055680,
    1133469505657562480137715318784, 1133469505657562480137715318784, 18841751140535665959544815616, 1118184676178206817917436166144, 121486602446151266186444144640, 35171763908420682558655868960768,
    3006147205210083459039032770560, 95638389159736103168051773440, 35171778540172108851689491005440, 98223210488377619469891010560, 98223210488377619469891010560, 1662040114316494982082629468160,
    90468746502453070564373299200, 3006147205210083459039032770560, 1662040114316494982082629468160, 1118176615766919559762749161472, 95638389159736103168051773440, 90468746502453070564373299200,
    121486602446151266186444144640, 35257167584132491011974833897472, 508301111439958964207815229440, 20733334808735168276897726464, 120115271892748016779541914583040, 418679599686071462623805702144,
    35257164907218606352697783222272, 419348416937966145471447564288, 375875295564811760374726524928, 508301111439958964207815229440, 20733334808735168276897726464, 16827114097311339685936040509440,
    81930626239994580715039621120, 16826348290581381479886382694400, 82735445751192955771179499520, 97682035774943032034795192320, 335325349041265392526227931136, 97682035774943032034795192320,
    1163102695347956270468113104896, 1163102695347956270468113104896, 290043631474280546694581977088, 37041487112992237912997232640, 37041487112992237912997232640, 15570964556636423770215546880,
    51935608901164451453992960, 8291374181064176166470942720, 82735445751192955771179499520, 8291374181064176166470942720, 51929682884630772260536320, 11004660710693714078088560640,
    413473373072394881744743956480, 413442101206445495535229992960, 11035932576643100287602524160, 97682035774943032034795192320
  ]
def negativeScales : Array ℕ := #[
    35, 30, 37, 38, 37, 51,
    29, 51, 28, 32, 33, 32,
    15, 15, 18, 46, 32, 53,
    37, 32, 56, 31, 31, 36,
    32, 37, 36, 51, 32, 32,
    32, 53, 34, 33, 58, 36,
    56, 37, 36, 34, 33, 53,
    35, 53, 34, 31, 32, 31,
    15, 15, 22, 10, 10, 9,
    21, 28, 34, 28, 23, 30,
    35, 36, 31, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35381297273130315, 30153892418750124, 37237787792480064, 38017184168071676, 37237787792480064, 51116737005622119,
    29729567087352263, 51116698445104969, 28743669790523215, 32263605776635796, 33043002152227407, 32263605776635796,
    15838588426008458, 15838588426008458, 18927919718345156, 46819001326807809, 32616711973801983, 53794188631839408,
    37245758503588644, 32271576487744375, 56794189232012636, 31310050635559011, 31310050635559011, 36390798049443377,
    32191406139060392, 37245758503588644, 36390798049443377, 51818990927132540, 32271576487744375, 32191406139060392,
    32616711973801983, 53797687521250513, 34681598137135022, 33065938839144284, 58566118628600456, 36401761375690035,
    56797687411713336, 37404064161559456, 36246168848978335, 34681598137135022, 33065938839144284, 53730558712826013,
    35048389499009471, 53730493053871658, 34062492202127653, 31302079924450431, 32081476300042043, 31302079924450431,
    15875821333629466, 15875821333629466, 22872184696592259, 10903128681431424, 10903128681431424, 9652844973024881,
    21424926413071481, 28743669790523215, 34062492202127653, 28743669790523215, 23424761787631594, 30152101322425877,
    35383709177204315, 36383600058999736, 31156195204619544, 31302079924450431
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
noncomputable def negativeCeiling : ℝ := 109901127877 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 412782703915845103995301396480, coefficient := (-412782703915845103995301396480) }, { argument := 11018331408259299489695662080, coefficient := (-11018331408259299489695662080) }, { argument := 2989584410691019638328073912320, coefficient := (-2989584410691019638328073912320) }, { argument := 10262720550920832934421133787136, coefficient := (-10262720550920832934421133787136) }, { argument := 2989584410691019638328073912320, coefficient := (-2989584410691019638328073912320) }, { argument := 2748975709569394235240611840000, coefficient := (-2748975709569394235240611840000) }, { argument := 8210718790197793129832120320, coefficient := (-8210718790197793129832120320) }, { argument := 2748902235615865806814323933184, coefficient := (-2748902235615865806814323933184) }, { argument := 8291374181064176166470942720, coefficient := (-8291374181064176166470942720) }, { argument := 95111455886128741718090055680, coefficient := (-95111455886128741718090055680) }, { argument := 326500997750705776933432459264, coefficient := (-326500997750705776933432459264) }, { argument := 95111455886128741718090055680, coefficient := (-95111455886128741718090055680) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 18841751140535665959544815616, coefficient := (-18841751140535665959544815616) }, { argument := 1118184676178206817917436166144, coefficient := (-1118184676178206817917436166144) }, { argument := 121486602446151266186444144640, coefficient := (-121486602446151266186444144640) }, { argument := 35171763908420682558655868960768, coefficient := (-35171763908420682558655868960768) }, { argument := 3006147205210083459039032770560, coefficient := (-3006147205210083459039032770560) }, { argument := 95638389159736103168051773440, coefficient := (-95638389159736103168051773440) }, { argument := 35171778540172108851689491005440, coefficient := (-35171778540172108851689491005440) }, { argument := 98223210488377619469891010560, coefficient := (-98223210488377619469891010560) }, { argument := 98223210488377619469891010560, coefficient := (-98223210488377619469891010560) }, { argument := 1662040114316494982082629468160, coefficient := (-1662040114316494982082629468160) }, { argument := 90468746502453070564373299200, coefficient := (-90468746502453070564373299200) }, { argument := 3006147205210083459039032770560, coefficient := (-3006147205210083459039032770560) }, { argument := 1662040114316494982082629468160, coefficient := (-1662040114316494982082629468160) }, { argument := 1118176615766919559762749161472, coefficient := (-1118176615766919559762749161472) }, { argument := 95638389159736103168051773440, coefficient := (-95638389159736103168051773440) }, { argument := 90468746502453070564373299200, coefficient := (-90468746502453070564373299200) }, { argument := 121486602446151266186444144640, coefficient := (-121486602446151266186444144640) }, { argument := 35257167584132491011974833897472, coefficient := (-35257167584132491011974833897472) }, { argument := 508301111439958964207815229440, coefficient := (-508301111439958964207815229440) }, { argument := 20733334808735168276897726464, coefficient := (-20733334808735168276897726464) }, { argument := 120115271892748016779541914583040, coefficient := (-120115271892748016779541914583040) }, { argument := 418679599686071462623805702144, coefficient := (-418679599686071462623805702144) }, { argument := 35257164907218606352697783222272, coefficient := (-35257164907218606352697783222272) }, { argument := 419348416937966145471447564288, coefficient := (-419348416937966145471447564288) }, { argument := 375875295564811760374726524928, coefficient := (-375875295564811760374726524928) }, { argument := 508301111439958964207815229440, coefficient := (-508301111439958964207815229440) }, { argument := 20733334808735168276897726464, coefficient := (-20733334808735168276897726464) }, { argument := 16827114097311339685936040509440, coefficient := (-16827114097311339685936040509440) }, { argument := 81930626239994580715039621120, coefficient := (-81930626239994580715039621120) }, { argument := 16826348290581381479886382694400, coefficient := (-16826348290581381479886382694400) }, { argument := 82735445751192955771179499520, coefficient := (-82735445751192955771179499520) }, { argument := 97682035774943032034795192320, coefficient := (-97682035774943032034795192320) }, { argument := 335325349041265392526227931136, coefficient := (-335325349041265392526227931136) }, { argument := 97682035774943032034795192320, coefficient := (-97682035774943032034795192320) }, { argument := 1163102695347956270468113104896, coefficient := (-1163102695347956270468113104896) }, { argument := 1163102695347956270468113104896, coefficient := (-1163102695347956270468113104896) }, { argument := 290043631474280546694581977088, coefficient := (-290043631474280546694581977088) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 51935608901164451453992960, coefficient := (-51935608901164451453992960) }, { argument := 8291374181064176166470942720, coefficient := (-8291374181064176166470942720) }, { argument := 82735445751192955771179499520, coefficient := (-82735445751192955771179499520) }, { argument := 8291374181064176166470942720, coefficient := (-8291374181064176166470942720) }, { argument := 51929682884630772260536320, coefficient := (-51929682884630772260536320) }, { argument := 11004660710693714078088560640, coefficient := (-11004660710693714078088560640) }, { argument := 413473373072394881744743956480, coefficient := (-413473373072394881744743956480) }, { argument := 413442101206445495535229992960, coefficient := (-413442101206445495535229992960) }, { argument := 11035932576643100287602524160, coefficient := (-11035932576643100287602524160) }, { argument := 97682035774943032034795192320, coefficient := (-97682035774943032034795192320) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7018341751440910894997317500272640)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4544505899, 2647676885, 534719115, 20090770805, 40178502595, 1072477245,
    89602959845, 153795647003, 89602959845, 58599, 58599, 4877299525,
    8371458235, 4877299525, 33321, 33321, 713, 180776925,
    6792253475, 13583479525, 362581275, 162065695645, 278171597923, 162065695645,
    60131, 60131, 89602959845, 153795647003, 89602959845, 938733,
    938733, 33373, 1149, 1149, 9085, 248672079165095,
    735522015, 240012447, 13563362614231105, 2423351481, 3978753004221775, 4854445299,
    2175596697, 735522015, 240012447, 2441581845237775, 890207915, 2441516587257841,
    449476295, 7677393, 58599, 58599, 33373, 805,
    58990365, 2216419555, 4432503845, 118315995, 5156002355, 8849827277,
    5156002355, 1915, 1915, 4877299525
  ]
def negativeCoefficients : Array ℕ := #[
    335325349041265392526227931136, 97682035774943032034795192320, 9863826665725466207154339840, 370609307283390627656373370880, 370581277317420045439871221760, 9891856631696048423656488960,
    1652882868507588673641402859520, 5674057879829832826167488413696, 1652882868507588673641402859520, 1133469505657562480137715318784, 1133469505657562480137715318784, 89970296108500161084679782400,
    308852295169586545747841515520, 89970296108500161084679782400, 644521875766064939686151847936, 644521875766064939686151847936, 13791425750163689625048055808, 13338982679628744337077043200,
    501179846148357432417871462400, 501141940856297570345733324800, 13376887971688606409215180800, 2989584410691019638328073912320, 10262720550920832934421133787136, 2989584410691019638328073912320,
    1163102695347956270468113104896, 1163102695347956270468113104896, 1652882868507588673641402859520, 5674057879829832826167488413696, 1652882868507588673641402859520, 18157736982788795024951243440128,
    18157736982788795024951243440128, 645527702047984311159507386368, 711196552569450967929546866688, 711196552569450967929546866688, 175729457139182496835289743360, 1119919483065368324061916037120,
    13567986371284157929346826240, 553431023039222231328620544, 3817747175958882560307500154880, 11175736142663003768119885824, 1119919409200776711770629734400, 11193588756309430291711131648,
    10033168869291706258280153088, 13567986371284157929346826240, 553431023039222231328620544, 2748976772101852880910784921600, 8210718790197793129832120320, 2748903298148324452484497014784,
    8291374181064176166470942720, 290043707032144272608905396224, 1133469505657562480137715318784, 1133469505657562480137715318784, 645527702047984311159507386368, 15570964556636423770215546880,
    544090082984856676907089920, 20442862145525105795992125440, 20441316008612137737786490880, 545636219897824735112724480, 95111455886128741718090055680, 326500997750705776933432459264,
    95111455886128741718090055680, 37041487112992237912997232640, 37041487112992237912997232640, 89970296108500161084679782400
  ]
def negativeScales : Array ℕ := #[
    32, 31, 28, 34, 35, 29,
    36, 37, 36, 15, 15, 32,
    32, 32, 15, 15, 9, 27,
    32, 33, 28, 37, 38, 37,
    15, 15, 36, 37, 36, 19,
    19, 15, 10, 10, 13, 47,
    29, 27, 53, 31, 51, 32,
    31, 29, 27, 51, 29, 51,
    28, 22, 15, 15, 15, 9,
    25, 31, 32, 26, 32, 33,
    32, 10, 10, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32081476300042043, 31302079924450431, 28994206031425411, 34225813864623199, 35225704746418620, 29998299915081063,
    36382827338334796, 37162223713926405, 36382827338334796, 15838588426008458, 15838588426008458, 32183435427951812,
    32962831816468606, 32183435427951812, 15024144077773686, 15024144077773686, 9477758266444015, 27429635297954808,
    32661243152761510, 33661134034556853, 28433729180148478, 37237787792480064, 38017184168071676, 37237787792480064,
    15875821333629466, 15875821333629466, 36382827338334796, 37162223713926405, 36382827338334796, 19840355352231019,
    19840355352231019, 15026393760123758, 10166163082646114, 10166163082646114, 13149270799121479, 47821237860645621,
    29454193282708223, 27838533986153479, 53590564412419061, 31174356521309839, 51821237765492276, 32176659307179260,
    31018763994598147, 29454193282708223, 27838533986153479, 51116737563251641, 29729567087352263, 51116699002749396,
    28743669790523215, 22872185072421736, 15838588426008458, 15838588426008458, 15026393760123758, 9652844973024881,
    25813976000867446, 31045583854789148, 32045474736584569, 26818069883134038, 32263605776635796, 33043002152227407,
    32263605776635796, 10903128681431424, 10903128681431424, 32183435427951812
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
noncomputable def negativeCeiling : ℝ := 4330899169 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 335325349041265392526227931136, coefficient := (-335325349041265392526227931136) }, { argument := 97682035774943032034795192320, coefficient := (-97682035774943032034795192320) }, { argument := 9863826665725466207154339840, coefficient := (-9863826665725466207154339840) }, { argument := 370609307283390627656373370880, coefficient := (-370609307283390627656373370880) }, { argument := 370581277317420045439871221760, coefficient := (-370581277317420045439871221760) }, { argument := 9891856631696048423656488960, coefficient := (-9891856631696048423656488960) }, { argument := 1652882868507588673641402859520, coefficient := (-1652882868507588673641402859520) }, { argument := 5674057879829832826167488413696, coefficient := (-5674057879829832826167488413696) }, { argument := 1652882868507588673641402859520, coefficient := (-1652882868507588673641402859520) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 89970296108500161084679782400, coefficient := (-89970296108500161084679782400) }, { argument := 308852295169586545747841515520, coefficient := (-308852295169586545747841515520) }, { argument := 89970296108500161084679782400, coefficient := (-89970296108500161084679782400) }, { argument := 644521875766064939686151847936, coefficient := (-644521875766064939686151847936) }, { argument := 644521875766064939686151847936, coefficient := (-644521875766064939686151847936) }, { argument := 13791425750163689625048055808, coefficient := (-13791425750163689625048055808) }, { argument := 13338982679628744337077043200, coefficient := (-13338982679628744337077043200) }, { argument := 501179846148357432417871462400, coefficient := (-501179846148357432417871462400) }, { argument := 501141940856297570345733324800, coefficient := (-501141940856297570345733324800) }, { argument := 13376887971688606409215180800, coefficient := (-13376887971688606409215180800) }, { argument := 2989584410691019638328073912320, coefficient := (-2989584410691019638328073912320) }, { argument := 10262720550920832934421133787136, coefficient := (-10262720550920832934421133787136) }, { argument := 2989584410691019638328073912320, coefficient := (-2989584410691019638328073912320) }, { argument := 1163102695347956270468113104896, coefficient := (-1163102695347956270468113104896) }, { argument := 1163102695347956270468113104896, coefficient := (-1163102695347956270468113104896) }, { argument := 1652882868507588673641402859520, coefficient := (-1652882868507588673641402859520) }, { argument := 5674057879829832826167488413696, coefficient := (-5674057879829832826167488413696) }, { argument := 1652882868507588673641402859520, coefficient := (-1652882868507588673641402859520) }, { argument := 18157736982788795024951243440128, coefficient := (-18157736982788795024951243440128) }, { argument := 18157736982788795024951243440128, coefficient := (-18157736982788795024951243440128) }, { argument := 645527702047984311159507386368, coefficient := (-645527702047984311159507386368) }, { argument := 711196552569450967929546866688, coefficient := (-711196552569450967929546866688) }, { argument := 711196552569450967929546866688, coefficient := (-711196552569450967929546866688) }, { argument := 175729457139182496835289743360, coefficient := (-175729457139182496835289743360) }, { argument := 1119919483065368324061916037120, coefficient := (-1119919483065368324061916037120) }, { argument := 13567986371284157929346826240, coefficient := (-13567986371284157929346826240) }, { argument := 553431023039222231328620544, coefficient := (-553431023039222231328620544) }, { argument := 3817747175958882560307500154880, coefficient := (-3817747175958882560307500154880) }, { argument := 11175736142663003768119885824, coefficient := (-11175736142663003768119885824) }, { argument := 1119919409200776711770629734400, coefficient := (-1119919409200776711770629734400) }, { argument := 11193588756309430291711131648, coefficient := (-11193588756309430291711131648) }, { argument := 10033168869291706258280153088, coefficient := (-10033168869291706258280153088) }, { argument := 13567986371284157929346826240, coefficient := (-13567986371284157929346826240) }, { argument := 553431023039222231328620544, coefficient := (-553431023039222231328620544) }, { argument := 2748976772101852880910784921600, coefficient := (-2748976772101852880910784921600) }, { argument := 8210718790197793129832120320, coefficient := (-8210718790197793129832120320) }, { argument := 2748903298148324452484497014784, coefficient := (-2748903298148324452484497014784) }, { argument := 8291374181064176166470942720, coefficient := (-8291374181064176166470942720) }, { argument := 290043707032144272608905396224, coefficient := (-290043707032144272608905396224) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 1133469505657562480137715318784, coefficient := (-1133469505657562480137715318784) }, { argument := 645527702047984311159507386368, coefficient := (-645527702047984311159507386368) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 544090082984856676907089920, coefficient := (-544090082984856676907089920) }, { argument := 20442862145525105795992125440, coefficient := (-20442862145525105795992125440) }, { argument := 20441316008612137737786490880, coefficient := (-20441316008612137737786490880) }, { argument := 545636219897824735112724480, coefficient := (-545636219897824735112724480) }, { argument := 95111455886128741718090055680, coefficient := (-95111455886128741718090055680) }, { argument := 326500997750705776933432459264, coefficient := (-326500997750705776933432459264) }, { argument := 95111455886128741718090055680, coefficient := (-95111455886128741718090055680) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 89970296108500161084679782400, coefficient := (-89970296108500161084679782400) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
