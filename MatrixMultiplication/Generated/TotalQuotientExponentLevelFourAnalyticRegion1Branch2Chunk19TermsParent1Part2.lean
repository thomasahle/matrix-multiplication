import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 19, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 105536935484229826714318679939481600
def positiveArguments : Array ℕ := #[
    14021, 135, 105, 15, 141, 1665,
    117, 105, 1665, 15, 117, 117,
    117, 117, 117, 135, 141, 4765,
    20013, 86723, 2859, 2859, 6671, 86723,
    86723, 2859, 1070219, 42885, 20013, 86723,
    6671, 42885, 6671, 86723, 86723, 2859,
    1603, 30457
  ]
def positiveCoefficients : Array ℕ := #[
    1110858066612500277399079727661056, 41780476325881584277845442560, 32495926031241232216102010880, 37138201178561408246973726720, 43637386384809654690194128896, 515292541352539539426760458240,
    1158711876771115937305580273664, 32495926031241232216102010880, 515292541352539539426760458240, 37138201178561408246973726720, 36209746149097373040799383552, 36209746149097373040799383552,
    36209746149097373040799383552, 1158711876771115937305580273664, 36209746149097373040799383552, 41780476325881584277845442560, 43637386384809654690194128896, 92168504487419328279598858240,
    1548430875388644715097260818432, 3354933563342063549377398439936, 110602205384903193935518629888, 1769635286158451102968298078208, 129035906282387059591438401536, 3354933563342063549377398439936,
    3354933563342063549377398439936, 1769635286158451102968298078208, 41402092215748762263195807121408, 3318066161547095818065558896640, 1548430875388644715097260818432, 3354933563342063549377398439936,
    129035906282387059591438401536, 3318066161547095818065558896640, 129035906282387059591438401536, 3354933563342063549377398439936, 3354933563342063549377398439936, 110602205384903193935518629888,
    992208941487232290331648065536, 1178248118016088344768832077824
  ]
def positiveScales : Array ℕ := #[
    13, 7, 6, 3, 7, 10,
    6, 6, 10, 3, 6, 6,
    6, 6, 6, 7, 7, 12,
    14, 16, 11, 11, 12, 16,
    16, 11, 20, 15, 14, 16,
    12, 15, 12, 16, 16, 11,
    10, 14
  ]
def negativeArguments : Array ℕ := #[
    2391182649, 1393128135, 89653269375, 89653226625, 117, 13946064125,
    13946057475, 117, 2941048285, 5048052259, 2941048285, 181298833625,
    181298747175, 117, 181298833625, 181298747175, 117, 117,
    8827142875, 6764123, 8827140025, 6764123, 2606399, 141,
    3, 953
  ]
def negativeCoefficients : Array ℕ := #[
    352876274876782855117992886272, 102794712672917160697937264640, 826905457765983643269857280000, 826905063466829067728191488000, 18104873074548686520399691776, 32157434468677141682716672000,
    32157419134821130411651891200, 18104873074548686520399691776, 108505530043634780736711557120, 372480512369937458180103602176, 108505530043634780736711557120, 836093296185605683750633472000,
    836092897505349390702949171200, 18104873074548686520399691776, 836093296185605683750633472000, 836092897505349390702949171200, 579355938385557968652790136832, 18104873074548686520399691776,
    40708011379298435841654784000, 62388022932046236702736384, 40707998235993283323599257600, 62388022932046236702736384, 24616742557169920830664081408, 21818693192404827345097064448,
    3802951800684688204490109616128, 75504438876093913726647384670208
  ]
def negativeScales : Array ℕ := #[
    31, 30, 36, 36, 6, 33,
    33, 6, 31, 32, 31, 37,
    37, 6, 37, 37, 6, 6,
    33, 22, 33, 22, 21, 7,
    1, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13775301627846313, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793, 10701306461953989,
    6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793, 12218260498797304,
    14288649826688701, 16404127044108637, 11481294904631088, 11481294904631088, 12703687325962645, 16404127044108637,
    16404127044108637, 11481294904631088, 20029474616310543, 15388185500239615, 14288649826688701, 16404127044108637,
    12703687325962645, 15388185500239615, 12703687325962645, 16404127044108637, 16404127044108637, 11481294904631088,
    10646558710153334, 14894486223353623
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31155077187608519, 30375680812016910, 36383637143513249, 36383636455582646, 6870364722125690, 33699138969312111,
    33699138281381506, 6870364722125690, 31453683324018234, 32233079699609792, 31453683324018234, 37399578687382274,
    37399577999451671, 6870364722125690, 37399578687382274, 37399577999451671, 6870364722125690, 6870364722125690,
    33039299403175480, 22689471463586864, 33039298937375663, 22689471463586864, 21313626524779940, 7139551352398794,
    1584962500724866, 9896332407999005
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 25150631667 / 125000000000
noncomputable def negativeCeiling : ℝ := 5906954461 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 352876274876782855117992886272, coefficient := (-352876274876782855117992886272) }, { argument := 102794712672917160697937264640, coefficient := (-102794712672917160697937264640) }, { argument := 826905457765983643269857280000, coefficient := (-826905457765983643269857280000) }, { argument := 826905063466829067728191488000, coefficient := (-826905063466829067728191488000) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 32157434468677141682716672000, coefficient := (-32157434468677141682716672000) }, { argument := 32157419134821130411651891200, coefficient := (-32157419134821130411651891200) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 108505530043634780736711557120, coefficient := (-108505530043634780736711557120) }, { argument := 372480512369937458180103602176, coefficient := (-372480512369937458180103602176) }, { argument := 108505530043634780736711557120, coefficient := (-108505530043634780736711557120) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 836093296185605683750633472000, coefficient := (-836093296185605683750633472000) }, { argument := 836092897505349390702949171200, coefficient := (-836092897505349390702949171200) }, { argument := 579355938385557968652790136832, coefficient := (-579355938385557968652790136832) }, { argument := 18104873074548686520399691776, coefficient := (-18104873074548686520399691776) }, { argument := 40708011379298435841654784000, coefficient := (-40708011379298435841654784000) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 40707998235993283323599257600, coefficient := (-40707998235993283323599257600) }, { argument := 62388022932046236702736384, coefficient := (-62388022932046236702736384) }, { argument := 24616742557169920830664081408, coefficient := (-24616742557169920830664081408) }, { argument := 21818693192404827345097064448, coefficient := (-21818693192404827345097064448) }, { argument := 1110858066612500277399079727661056, coefficient := 1110858066612500277399079727661056 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 43637386384809654690194128896, coefficient := 43637386384809654690194128896 }, { argument := 515292541352539539426760458240, coefficient := 515292541352539539426760458240 }, { argument := 1158711876771115937305580273664, coefficient := 1158711876771115937305580273664 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 515292541352539539426760458240, coefficient := 515292541352539539426760458240 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 1158711876771115937305580273664, coefficient := 1158711876771115937305580273664 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 43637386384809654690194128896, coefficient := 43637386384809654690194128896 }, { argument := 3802951800684688204490109616128, coefficient := (-3802951800684688204490109616128) }, { argument := 92168504487419328279598858240, coefficient := 92168504487419328279598858240 }, { argument := 1548430875388644715097260818432, coefficient := 1548430875388644715097260818432 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 110602205384903193935518629888, coefficient := 110602205384903193935518629888 }, { argument := 1769635286158451102968298078208, coefficient := 1769635286158451102968298078208 }, { argument := 129035906282387059591438401536, coefficient := 129035906282387059591438401536 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 1769635286158451102968298078208, coefficient := 1769635286158451102968298078208 }, { argument := 41402092215748762263195807121408, coefficient := 41402092215748762263195807121408 }, { argument := 3318066161547095818065558896640, coefficient := 3318066161547095818065558896640 }, { argument := 1548430875388644715097260818432, coefficient := 1548430875388644715097260818432 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 129035906282387059591438401536, coefficient := 129035906282387059591438401536 }, { argument := 3318066161547095818065558896640, coefficient := 3318066161547095818065558896640 }, { argument := 129035906282387059591438401536, coefficient := 129035906282387059591438401536 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 3354933563342063549377398439936, coefficient := 3354933563342063549377398439936 }, { argument := 110602205384903193935518629888, coefficient := 110602205384903193935518629888 }, { argument := 75504438876093913726647384670208, coefficient := (-75504438876093913726647384670208) }, { argument := 992208941487232290331648065536, coefficient := 992208941487232290331648065536 }, { argument := 1178248118016088344768832077824, coefficient := 1178248118016088344768832077824 }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-49427884387971123678981402197491712)
def positiveArguments : Array ℕ := #[
    46487, 479297, 14427, 46487, 14427, 14427,
    1235913, 14427, 479297, 1235913, 1603, 14427,
    14427, 30457, 1275, 22695, 1275, 40375,
    68935, 1275, 68935, 68935, 22695, 1275,
    483, 541, 483, 541, 1, 9273607097,
    9273605191, 34708233605, 15582796329, 34708230451, 278823509, 10348494251,
    20696497931, 558137589, 5584953, 220569117, 17688510901, 110284559,
    11168769, 789107, 66319757, 33159873, 394559
  ]
def positiveCoefficients : Array ℕ := #[
    899189353222804263113056059392, 9270952297021326712786336612352, 1116235059173136326623104073728, 899189353222804263113056059392, 1116235059173136326623104073728, 1116235059173136326623104073728,
    47812068367916005990356291158016, 1116235059173136326623104073728, 9270952297021326712786336612352, 47812068367916005990356291158016, 992208941487232290331648065536, 1116235059173136326623104073728,
    1116235059173136326623104073728, 1178248118016088344768832077824, 98648346880553740656023961600, 1755940574473856583677226516480, 98648346880553740656023961600, 1561932158942100893720379392000,
    2666793644004302789067847761920, 98648346880553740656023961600, 2666793644004302789067847761920, 2666793644004302789067847761920, 1755940574473856583677226516480, 98648346880553740656023961600,
    149481259743709668194069250048, 167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 5070602400912917605986812821504, 87586742660349741559206614401024,
    87586724658688708860119059791872, 163904999055861876840430913454080, 588701400747629990572115594575872, 163904984161517989869569909456896, 10533654348301622944542188634112, 390955059192732907810741779693568,
    390945792568541436431853267451904, 10542920972493094323430700875776, 52748389711204547290334232576, 8332865642215626167105624211456, 83531631010756749124464170500096, 8332865679994558030062785921024,
    52743020380513524503726260224, 7452904896395634251288018944, 626372395217719066497063583744, 626372291325656443364868882432, 7453008788458257383482720256
  ]
def positiveScales : Array ℕ := #[
    15, 18, 13, 15, 13, 13,
    20, 13, 18, 20, 10, 13,
    13, 14, 10, 14, 10, 15,
    16, 10, 16, 16, 14, 10,
    8, 9, 8, 9, 0, 33,
    33, 35, 33, 35, 28, 33,
    34, 29, 22, 27, 34, 26,
    23, 19, 25, 24, 18
  ]
def negativeArguments : Array ℕ := #[
    1603, 85, 1, 1, 2211, 723,
    10135, 633, 1
  ]
def negativeCoefficients : Array ℕ := #[
    127002744510365733162450952388608, 13468787627424937390902471557120, 633825300114114700748351602688, 5070602400912917605986812821504, 175173467319038450419325674192896, 916511383965009857282116417486848,
    802977427082069061510567936655360, 100302853743058651393426641125376, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    10, 6, 0, 0, 11, 9,
    13, 9, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15504539705282100, 18870560384194823, 13816483711541072, 15504539705282100, 13816483711541072, 13816483711541072,
    20237145760069582, 13816483711541072, 18870560384194823, 20237145760069582, 10646558710153334, 13816483711541072,
    13816483711541072, 14894486223353623, 10316281531746219, 14470086867825249, 10316281531746219, 15301174639356011,
    16072949040354974, 10316281531746219, 16072949040354974, 16072949040354974, 14470086867825249, 10316281531746219,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 0, 33110483458074441,
    33110483161557994, 35014558893292492, 33859235096650432, 35014558762192177, 28054776966244435, 33268701813733540,
    34268667617805150, 29056045570220628, 22413113709128155, 27716655565116907, 34042093549408064, 26716655571657691,
    23412966847753171, 19589861412068196, 25982935383814816, 24982935144524940, 18589881522819768
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10646558710174063, 6409390936137712, 0, 0, 11110483309816226, 9497851836951370,
    13307058468354262, 9306061689428342, 0
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 422472381499 / 500000000000
noncomputable def negativeCeiling : ℝ := 285378427883 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 899189353222804263113056059392, coefficient := 899189353222804263113056059392 }, { argument := 9270952297021326712786336612352, coefficient := 9270952297021326712786336612352 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 899189353222804263113056059392, coefficient := 899189353222804263113056059392 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 47812068367916005990356291158016, coefficient := 47812068367916005990356291158016 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 9270952297021326712786336612352, coefficient := 9270952297021326712786336612352 }, { argument := 47812068367916005990356291158016, coefficient := 47812068367916005990356291158016 }, { argument := 992208941487232290331648065536, coefficient := 992208941487232290331648065536 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 1116235059173136326623104073728, coefficient := 1116235059173136326623104073728 }, { argument := 1178248118016088344768832077824, coefficient := 1178248118016088344768832077824 }, { argument := 127002744510365733162450952388608, coefficient := (-127002744510365733162450952388608) }, { argument := 98648346880553740656023961600, coefficient := 98648346880553740656023961600 }, { argument := 1755940574473856583677226516480, coefficient := 1755940574473856583677226516480 }, { argument := 98648346880553740656023961600, coefficient := 98648346880553740656023961600 }, { argument := 1561932158942100893720379392000, coefficient := 1561932158942100893720379392000 }, { argument := 2666793644004302789067847761920, coefficient := 2666793644004302789067847761920 }, { argument := 98648346880553740656023961600, coefficient := 98648346880553740656023961600 }, { argument := 2666793644004302789067847761920, coefficient := 2666793644004302789067847761920 }, { argument := 2666793644004302789067847761920, coefficient := 2666793644004302789067847761920 }, { argument := 1755940574473856583677226516480, coefficient := 1755940574473856583677226516480 }, { argument := 98648346880553740656023961600, coefficient := 98648346880553740656023961600 }, { argument := 13468787627424937390902471557120, coefficient := (-13468787627424937390902471557120) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 5070602400912917605986812821504, coefficient := 5070602400912917605986812821504 }, { argument := 5070602400912917605986812821504, coefficient := (-5070602400912917605986812821504) }, { argument := 87586742660349741559206614401024, coefficient := 87586742660349741559206614401024 }, { argument := 87586724658688708860119059791872, coefficient := 87586724658688708860119059791872 }, { argument := 175173467319038450419325674192896, coefficient := (-175173467319038450419325674192896) }, { argument := 163904999055861876840430913454080, coefficient := 163904999055861876840430913454080 }, { argument := 588701400747629990572115594575872, coefficient := 588701400747629990572115594575872 }, { argument := 163904984161517989869569909456896, coefficient := 163904984161517989869569909456896 }, { argument := 916511383965009857282116417486848, coefficient := (-916511383965009857282116417486848) }, { argument := 10533654348301622944542188634112, coefficient := 10533654348301622944542188634112 }, { argument := 390955059192732907810741779693568, coefficient := 390955059192732907810741779693568 }, { argument := 390945792568541436431853267451904, coefficient := 390945792568541436431853267451904 }, { argument := 10542920972493094323430700875776, coefficient := 10542920972493094323430700875776 }, { argument := 802977427082069061510567936655360, coefficient := (-802977427082069061510567936655360) }, { argument := 52748389711204547290334232576, coefficient := 52748389711204547290334232576 }, { argument := 8332865642215626167105624211456, coefficient := 8332865642215626167105624211456 }, { argument := 83531631010756749124464170500096, coefficient := 83531631010756749124464170500096 }, { argument := 8332865679994558030062785921024, coefficient := 8332865679994558030062785921024 }, { argument := 52743020380513524503726260224, coefficient := 52743020380513524503726260224 }, { argument := 100302853743058651393426641125376, coefficient := (-100302853743058651393426641125376) }, { argument := 7452904896395634251288018944, coefficient := 7452904896395634251288018944 }, { argument := 626372395217719066497063583744, coefficient := 626372395217719066497063583744 }, { argument := 626372291325656443364868882432, coefficient := 626372291325656443364868882432 }, { argument := 7453008788458257383482720256, coefficient := 7453008788458257383482720256 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk19
