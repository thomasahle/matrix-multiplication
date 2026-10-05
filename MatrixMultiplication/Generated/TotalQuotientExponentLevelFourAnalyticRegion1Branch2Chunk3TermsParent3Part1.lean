import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-139173889006088516685861125881856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8091, 371924928391, 14229, 170289, 254745, 73899,
    14229, 295137, 148257, 14229, 170289, 14229,
    8091, 96831, 144855, 42021, 8091, 167823,
    84303, 8091, 96831, 8091, 77932233, 6553262391,
    3276630405, 38966907, 14601, 174741, 261405, 75831,
    14601, 302853, 152133, 14601, 174741, 14601,
    227943, 2727963, 4080915, 1183833, 227943, 4727979,
    2375019, 227943, 2727963, 227943, 3647731293, 306734959011,
    153367442505, 1823902647, 279, 3339, 4995, 1449,
    279, 5787, 2907, 279, 3339, 279,
    993007485, 83501246595, 41750613225, 496513815
  ]
def negativeCoefficients : Array ℕ := #[
    76417334425796598848028672, 209375121113938251053268992, 134389105369504363491360768, 3216668264005556055180312576, 2405998499357255539925975040, 2791825285740671293175365632,
    134389105369504363491360768, 2787490153309396958869192704, 2800495550603219961787711488, 134389105369504363491360768, 3216668264005556055180312576, 134389105369504363491360768,
    76417334425796598848028672, 1829085875611002462749589504, 1368116793752164914859868160, 1587508495813322892197756928, 76417334425796598848028672, 1585043420509264937396207616,
    1592438646421438801800855552, 76417334425796598848028672, 1829085875611002462749589504, 76417334425796598848028672, 179699494655462743857954816, 15110794271830367057825759232,
    15110790626292569490975621120, 179703140193260310708092928, 137902546032759379530350592, 3300764166332498697145810944, 2468900420909079214172405760, 2864814182099904529598251008,
    137902546032759379530350592, 2860365712873041323806949376, 2873711120553630941180854272, 137902546032759379530350592, 3300764166332498697145810944, 137902546032759379530350592,
    2152860766409511077891014656, 51529764150834103864359124992, 38543152430879956394500423680, 44723946244120165618123014144, 2152860766409511077891014656, 44654499122623084615610400768,
    44862840487114327623148240896, 2152860766409511077891014656, 51529764150834103864359124992, 2152860766409511077891014656, 8411095701454078752835239936, 707282660916963309706618601472,
    707282490282274784884052459520, 8411266336142603575401381888, 84322575918120384935755776, 2018301655846623407171960832, 1509646117243768181914337280, 1751733512621597674149249024,
    84322575918120384935755776, 1749013429527464758506160128, 1757173678809863505435426816, 84322575918120384935755776, 2018301655846623407171960832, 84322575918120384935755776,
    2289719367384122058835230720, 192540765721709515736812093440, 192540719270502095126947430400, 2289765818591542668699893760
  ]
def negativeScales : Array ℕ := #[
    12, 38, 13, 17, 17, 16,
    13, 18, 17, 13, 17, 13,
    12, 16, 17, 15, 12, 17,
    16, 12, 16, 12, 26, 32,
    31, 25, 13, 17, 17, 16,
    13, 18, 17, 13, 17, 13,
    17, 21, 21, 20, 17, 22,
    21, 17, 21, 17, 31, 38,
    37, 30, 8, 11, 12, 10,
    8, 12, 11, 8, 11, 8,
    29, 36, 35, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12982102324703674, 38436220492062607, 13796546654402698, 17377625720034614, 17958694316714768, 16173267221528426,
    13796546654402698, 18171025270741756, 17177740698107733, 13796546654402698, 17377625720034614, 13796546654402698,
    12982102324703674, 16563181373192661, 17144249957807353, 15358822874684503, 12982102324703674, 17356580923897833,
    16363296351263811, 12982102324703674, 16563181373192661, 12982102324703674, 26215716818829221, 32609566152029595,
    31609565803973772, 25215746086279107, 13833779561266426, 17414858626233599, 17995927233034729, 16210500127727401,
    13833779561266426, 18208258176940731, 17214973604306709, 13833779561266426, 17414858626233599, 13833779561266426,
    17798313580599046, 21379392646208802, 21960461243250186, 20175034147702613, 17798313580599046, 22172792196915944,
    21179507624281921, 17798313580599046, 21379392646208802, 17798313580599046, 31764352312815846, 38158201645702112,
    37158201297646289, 30764381580265924, 8124121311829188, 11705200378144884, 12286268962679781, 10500841879557209,
    8124121311829188, 12498599928770519, 11505315356136561, 8124121311829188, 11705200378144884, 8124121311829188,
    29887229354974391, 36281078684699833, 35281078336644010, 28887258622426125
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
noncomputable def negativeCeiling : ℝ := 910721449 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 209375121113938251053268992, coefficient := (-209375121113938251053268992) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 1368116793752164914859868160, coefficient := (-1368116793752164914859868160) }, { argument := 1587508495813322892197756928, coefficient := (-1587508495813322892197756928) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1585043420509264937396207616, coefficient := (-1585043420509264937396207616) }, { argument := 1592438646421438801800855552, coefficient := (-1592438646421438801800855552) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 179699494655462743857954816, coefficient := (-179699494655462743857954816) }, { argument := 15110794271830367057825759232, coefficient := (-15110794271830367057825759232) }, { argument := 15110790626292569490975621120, coefficient := (-15110790626292569490975621120) }, { argument := 179703140193260310708092928, coefficient := (-179703140193260310708092928) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 2468900420909079214172405760, coefficient := (-2468900420909079214172405760) }, { argument := 2864814182099904529598251008, coefficient := (-2864814182099904529598251008) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2860365712873041323806949376, coefficient := (-2860365712873041323806949376) }, { argument := 2873711120553630941180854272, coefficient := (-2873711120553630941180854272) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 51529764150834103864359124992, coefficient := (-51529764150834103864359124992) }, { argument := 38543152430879956394500423680, coefficient := (-38543152430879956394500423680) }, { argument := 44723946244120165618123014144, coefficient := (-44723946244120165618123014144) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 44654499122623084615610400768, coefficient := (-44654499122623084615610400768) }, { argument := 44862840487114327623148240896, coefficient := (-44862840487114327623148240896) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 51529764150834103864359124992, coefficient := (-51529764150834103864359124992) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 8411095701454078752835239936, coefficient := (-8411095701454078752835239936) }, { argument := 707282660916963309706618601472, coefficient := (-707282660916963309706618601472) }, { argument := 707282490282274784884052459520, coefficient := (-707282490282274784884052459520) }, { argument := 8411266336142603575401381888, coefficient := (-8411266336142603575401381888) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 1509646117243768181914337280, coefficient := (-1509646117243768181914337280) }, { argument := 1751733512621597674149249024, coefficient := (-1751733512621597674149249024) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1749013429527464758506160128, coefficient := (-1749013429527464758506160128) }, { argument := 1757173678809863505435426816, coefficient := (-1757173678809863505435426816) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2289719367384122058835230720, coefficient := (-2289719367384122058835230720) }, { argument := 192540765721709515736812093440, coefficient := (-192540765721709515736812093440) }, { argument := 192540719270502095126947430400, coefficient := (-192540719270502095126947430400) }, { argument := 2289765818591542668699893760, coefficient := (-2289765818591542668699893760) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-506044845312092636087756297076736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    79978629, 4250966343, 170289, 40517219565, 174741, 5565,
    170289, 96831, 174741, 2727963, 3339, 4250966343,
    170289, 5565, 3339, 5565, 85701, 96831,
    79978629, 2043882103, 1909180809, 2043882103, 1909180809, 19558217812179,
    8332964925, 113847389490989, 12880710975, 409892865, 12879727935, 8815309395,
    19620381759699, 8332964925, 49339515, 78093805517763, 4081708125406269, 1813441875,
    1606191375, 75180118875, 20465986875, 2040854786355933, 75180118875, 1813441875,
    1813441875, 777189375, 1813441875, 20465986875, 777189375, 39046179106083,
    1606191375, 14229, 170289, 254745, 73899, 14229,
    295137, 148257, 14229, 170289, 14229, 3647731293,
    306734959011, 153367442505, 1823902647, 2097362413689
  ]
def negativeCoefficients : Array ℕ := #[
    368836325132291220613103616, 39208244097637007538618630144, 3216668264005556055180312576, 373705389946926223431586283520, 3300764166332498697145810944, 105119877908678302456872960,
    3216668264005556055180312576, 1829085875611002462749589504, 3300764166332498697145810944, 51529764150834103864359124992, 2018301655846623407171960832, 39208244097637007538618630144,
    3216668264005556055180312576, 105119877908678302456872960, 2018301655846623407171960832, 105119877908678302456872960, 3237692239587291715671687168, 1829085875611002462749589504,
    368836325132291220613103616, 4712871258859533171012141056, 4402271221757594673157767168, 4712871258859533171012141056, 4402271221757594673157767168, 22020595612740085480943517696,
    38429017836668327063401267200, 256361530444360891338978230272, 59401794710811707615635046400, 1890297194573644822436904960, 59397261238988152756229898240, 40653439085033095715440558080,
    22090585995461823248178610176, 38429017836668327063401267200, 1820306811851907055201812480, 43962904178717678905438765056, 2297797399076849853186523004928, 16726049080336493743964160000,
    14814500614012323030368256000, 693414206159092926356914176000, 188765411049511857967595520000, 2297798213837468270740679688192, 693414206159092926356914176000, 16726049080336493743964160000,
    16726049080336493743964160000, 14336613497431280351969280000, 16726049080336493743964160000, 188765411049511857967595520000, 14336613497431280351969280000, 43962089418099261351282081792,
    14814500614012323030368256000, 134389105369504363491360768, 3216668264005556055180312576, 2405998499357255539925975040, 2791825285740671293175365632, 134389105369504363491360768,
    2787490153309396958869192704, 2800495550603219961787711488, 134389105369504363491360768, 3216668264005556055180312576, 134389105369504363491360768, 8411095701454078752835239936,
    707282660916963309706618601472, 707282490282274784884052459520, 8411266336142603575401381888, 2361420146187666119706279936
  ]
def negativeScales : Array ℕ := #[
    26, 31, 17, 35, 17, 12,
    17, 16, 17, 21, 11, 31,
    17, 12, 11, 12, 16, 16,
    26, 30, 30, 30, 30, 44,
    32, 46, 33, 28, 33, 33,
    44, 32, 25, 46, 51, 30,
    30, 36, 34, 50, 36, 30,
    30, 29, 30, 34, 29, 45,
    30, 13, 17, 17, 16, 13,
    18, 17, 13, 17, 13, 31,
    38, 37, 30, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26253111214778760, 31985143709125029, 17377625720034614, 35237816123569972, 17414858626233599, 12442165972229357,
    17377625720034614, 16563181373192661, 17414858626233599, 21379392646208802, 11705200378144884, 31985143709125029,
    17377625720034614, 12442165972229357, 11705200378144884, 12442165972229357, 16387024418036865, 16563181373192661,
    26253111214778760, 30928664841098771, 30830306594839619, 30928664841098771, 30830306594839619, 44152840148270014,
    32956182773091720, 46694094539489923, 33584493176786173, 28610671636323113, 33584383067875468, 33037364059356901,
    44157418346319486, 32956182773091720, 25556240198445952, 46150273350363517, 51858094447219829, 30756083358584448,
    30580996651772961, 36129632145449518, 34252509184447239, 50858094958775348, 36129632145449518, 30756083358584448,
    30756083358584448, 29533690936992097, 30756083358584448, 34252509184447239, 29533690936992097, 45150246612776043,
    30580996651772961, 13796546654402698, 17377625720034614, 17958694316714768, 16173267221528426, 13796546654402698,
    18171025270741756, 17177740698107733, 13796546654402698, 17377625720034614, 13796546654402698, 31764352312815846,
    38158201645702112, 37158201297646289, 30764381580265924, 40931713319708264
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
noncomputable def negativeCeiling : ℝ := 2412072557 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 368836325132291220613103616, coefficient := (-368836325132291220613103616) }, { argument := 39208244097637007538618630144, coefficient := (-39208244097637007538618630144) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 373705389946926223431586283520, coefficient := (-373705389946926223431586283520) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 3300764166332498697145810944, coefficient := (-3300764166332498697145810944) }, { argument := 51529764150834103864359124992, coefficient := (-51529764150834103864359124992) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 39208244097637007538618630144, coefficient := (-39208244097637007538618630144) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 2018301655846623407171960832, coefficient := (-2018301655846623407171960832) }, { argument := 105119877908678302456872960, coefficient := (-105119877908678302456872960) }, { argument := 3237692239587291715671687168, coefficient := (-3237692239587291715671687168) }, { argument := 1829085875611002462749589504, coefficient := (-1829085875611002462749589504) }, { argument := 368836325132291220613103616, coefficient := (-368836325132291220613103616) }, { argument := 4712871258859533171012141056, coefficient := (-4712871258859533171012141056) }, { argument := 4402271221757594673157767168, coefficient := (-4402271221757594673157767168) }, { argument := 4712871258859533171012141056, coefficient := (-4712871258859533171012141056) }, { argument := 4402271221757594673157767168, coefficient := (-4402271221757594673157767168) }, { argument := 22020595612740085480943517696, coefficient := (-22020595612740085480943517696) }, { argument := 38429017836668327063401267200, coefficient := (-38429017836668327063401267200) }, { argument := 256361530444360891338978230272, coefficient := (-256361530444360891338978230272) }, { argument := 59401794710811707615635046400, coefficient := (-59401794710811707615635046400) }, { argument := 1890297194573644822436904960, coefficient := (-1890297194573644822436904960) }, { argument := 59397261238988152756229898240, coefficient := (-59397261238988152756229898240) }, { argument := 40653439085033095715440558080, coefficient := (-40653439085033095715440558080) }, { argument := 22090585995461823248178610176, coefficient := (-22090585995461823248178610176) }, { argument := 38429017836668327063401267200, coefficient := (-38429017836668327063401267200) }, { argument := 1820306811851907055201812480, coefficient := (-1820306811851907055201812480) }, { argument := 43962904178717678905438765056, coefficient := (-43962904178717678905438765056) }, { argument := 2297797399076849853186523004928, coefficient := (-2297797399076849853186523004928) }, { argument := 16726049080336493743964160000, coefficient := (-16726049080336493743964160000) }, { argument := 14814500614012323030368256000, coefficient := (-14814500614012323030368256000) }, { argument := 693414206159092926356914176000, coefficient := (-693414206159092926356914176000) }, { argument := 188765411049511857967595520000, coefficient := (-188765411049511857967595520000) }, { argument := 2297798213837468270740679688192, coefficient := (-2297798213837468270740679688192) }, { argument := 693414206159092926356914176000, coefficient := (-693414206159092926356914176000) }, { argument := 16726049080336493743964160000, coefficient := (-16726049080336493743964160000) }, { argument := 16726049080336493743964160000, coefficient := (-16726049080336493743964160000) }, { argument := 14336613497431280351969280000, coefficient := (-14336613497431280351969280000) }, { argument := 16726049080336493743964160000, coefficient := (-16726049080336493743964160000) }, { argument := 188765411049511857967595520000, coefficient := (-188765411049511857967595520000) }, { argument := 14336613497431280351969280000, coefficient := (-14336613497431280351969280000) }, { argument := 43962089418099261351282081792, coefficient := (-43962089418099261351282081792) }, { argument := 14814500614012323030368256000, coefficient := (-14814500614012323030368256000) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 2405998499357255539925975040, coefficient := (-2405998499357255539925975040) }, { argument := 2791825285740671293175365632, coefficient := (-2791825285740671293175365632) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 2787490153309396958869192704, coefficient := (-2787490153309396958869192704) }, { argument := 2800495550603219961787711488, coefficient := (-2800495550603219961787711488) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 3216668264005556055180312576, coefficient := (-3216668264005556055180312576) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 8411095701454078752835239936, coefficient := (-8411095701454078752835239936) }, { argument := 707282660916963309706618601472, coefficient := (-707282660916963309706618601472) }, { argument := 707282490282274784884052459520, coefficient := (-707282490282274784884052459520) }, { argument := 8411266336142603575401381888, coefficient := (-8411266336142603575401381888) }, { argument := 2361420146187666119706279936, coefficient := (-2361420146187666119706279936) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
