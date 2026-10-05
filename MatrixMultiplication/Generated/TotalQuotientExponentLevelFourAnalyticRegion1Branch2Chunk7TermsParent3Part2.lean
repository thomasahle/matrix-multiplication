import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10860378014973823829171548553478144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10023, 10023, 10023, 10023, 11565, 12079,
    37091439, 5921544123, 236352422097, 5921544123, 148348827, 313002333,
    11760301731, 23518824549, 627783579, 16623117, 2653833969, 105925088691,
    2653833969, 66484881, 10592657901, 397993369107, 795926536053, 21245517963,
    134834653485, 231431894739, 134834653485, 576583245, 21663713715, 43324150485,
    1156443435, 76670685315, 131598528381, 76670685315, 20173871, 23923,
    20173871, 12079, 5619915, 897203655, 35810973045, 897203655,
    22477095, 19159037541, 719854258587, 1439599628973, 38426963283, 138359742465,
    237482401791, 138359742465, 10592657901, 397993369107, 795926536053, 21245517963,
    2159998272495, 3707448196113, 2159998272495, 942581291, 282495, 942581291,
    142635, 2643816735, 4537880289, 2643816735
  ]
def negativeCoefficients : Array ℕ := #[
    189329117031209815907500032, 189329117031209815907500032, 6058531744998714109040001024, 189329117031209815907500032, 218456673497549787585576960, 228165858986329778144935936,
    171054070639652334370553856, 27308302239539968545172488192, 272495790101545826507840028672, 27308302239539968545172488192, 171034552831500845058097152, 5773873931325013620191920128,
    216939276261360431460878647296, 216922868684940234021081710592, 5790281507745211059988856832, 153321192503165250265153536, 24477298020129923959149821952, 244246625258482862037330296832,
    24477298020129923959149821952, 153303698072254345969139712, 97700024680052204152194859008, 3670840911475125195509078163456, 3670563278010962380935672102912, 97977658144215018725600919552,
    1243630172552552345339040890880, 4269164932744021006852999348224, 1243630172552552345339040890880, 5318041778851986229124136960, 199812491293358292135019806720, 199797379051918636598364733440,
    5333154020291641765779210240, 707162254980863098330042859520, 2427564373521109984288960413696, 707162254980863098330042859520, 95268412240135932356870537216, 225946346739381044894498816,
    95268412240135932356870537216, 228165858986329778144935936, 207338267442002829540065280, 33100972411563598236572712960, 330297927395813123039806095360, 33100972411563598236572712960,
    207314609492728297040117760, 176710931108710285270610608128, 6639483639262162678657943863296, 6638981481068039267539948142592, 177213089302833696388606328832, 1276143379678109269400192286720,
    4380777087848439856705365344256, 1276143379678109269400192286720, 97700024680052204152194859008, 3670840911475125195509078163456, 3670563278010962380935672102912, 97977658144215018725600919552,
    19922467666185005218470517800960, 68390348040232650247037264068608, 19922467666185005218470517800960, 4451214295998399570237546561536, 2668089839156520849286103040, 4451214295998399570237546561536,
    2694298973136447380222115840, 780316971013366177467633500160, 2678691722506052396456783904768, 780316971013366177467633500160
  ]
def negativeScales : Array ℕ := #[
    13, 13, 13, 13, 13, 13,
    25, 32, 37, 32, 27, 28,
    33, 34, 29, 23, 31, 36,
    31, 25, 33, 38, 39, 34,
    36, 37, 36, 29, 34, 35,
    30, 36, 36, 36, 24, 14,
    24, 13, 22, 29, 35, 29,
    24, 34, 39, 40, 35, 37,
    37, 37, 33, 38, 39, 34,
    40, 41, 40, 29, 18, 29,
    17, 31, 32, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13291026768056127, 13291026768056127, 13291026768056127, 13291026768056127, 13497477645523802, 13560213400873323,
    25144582903955730, 32463326281211855, 37782148693458873, 32463326281211855, 27144418278515843, 28221598169595408,
    33453206024373895, 34453096906169316, 29225692051789075, 23986687610492467, 31305430968630666, 36624253380441719,
    31305430968630666, 25986522985001701, 33302345583479770, 38533953438259016, 39533844320054434, 34306439465673437,
    36972400386179081, 37751796746862514, 36972400386179081, 29102953673096789, 34334561527875224, 35334452409670645,
    30107047555290456, 36157956024193105, 36937352408190777, 36157956024193105, 24265984601740514, 14546110697754515,
    24265984601740514, 13560213400873323, 22422116879484655, 29740860256924610, 35059682668540829, 29740860256924610,
    24421952254044768, 34157306037625041, 39388913892403480, 40388804774198901, 35161399919818708, 37009633277236003,
    37789029653343312, 37009633277236003, 33302345583479770, 38533953438259016, 39533844320054434, 34306439465673437,
    40974167312799453, 41753563673045874, 40974167312799453, 29812041805959772, 18107865807313164, 29812041805959772,
    17121968510431347, 31299975029065533, 32079371404657144, 31299975029065533
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
noncomputable def negativeCeiling : ℝ := 8113939621 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 6058531744998714109040001024, coefficient := (-6058531744998714109040001024) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }, { argument := 218456673497549787585576960, coefficient := (-218456673497549787585576960) }, { argument := 228165858986329778144935936, coefficient := (-228165858986329778144935936) }, { argument := 171054070639652334370553856, coefficient := (-171054070639652334370553856) }, { argument := 27308302239539968545172488192, coefficient := (-27308302239539968545172488192) }, { argument := 272495790101545826507840028672, coefficient := (-272495790101545826507840028672) }, { argument := 27308302239539968545172488192, coefficient := (-27308302239539968545172488192) }, { argument := 171034552831500845058097152, coefficient := (-171034552831500845058097152) }, { argument := 5773873931325013620191920128, coefficient := (-5773873931325013620191920128) }, { argument := 216939276261360431460878647296, coefficient := (-216939276261360431460878647296) }, { argument := 216922868684940234021081710592, coefficient := (-216922868684940234021081710592) }, { argument := 5790281507745211059988856832, coefficient := (-5790281507745211059988856832) }, { argument := 153321192503165250265153536, coefficient := (-153321192503165250265153536) }, { argument := 24477298020129923959149821952, coefficient := (-24477298020129923959149821952) }, { argument := 244246625258482862037330296832, coefficient := (-244246625258482862037330296832) }, { argument := 24477298020129923959149821952, coefficient := (-24477298020129923959149821952) }, { argument := 153303698072254345969139712, coefficient := (-153303698072254345969139712) }, { argument := 97700024680052204152194859008, coefficient := (-97700024680052204152194859008) }, { argument := 3670840911475125195509078163456, coefficient := (-3670840911475125195509078163456) }, { argument := 3670563278010962380935672102912, coefficient := (-3670563278010962380935672102912) }, { argument := 97977658144215018725600919552, coefficient := (-97977658144215018725600919552) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 4269164932744021006852999348224, coefficient := (-4269164932744021006852999348224) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 5318041778851986229124136960, coefficient := (-5318041778851986229124136960) }, { argument := 199812491293358292135019806720, coefficient := (-199812491293358292135019806720) }, { argument := 199797379051918636598364733440, coefficient := (-199797379051918636598364733440) }, { argument := 5333154020291641765779210240, coefficient := (-5333154020291641765779210240) }, { argument := 707162254980863098330042859520, coefficient := (-707162254980863098330042859520) }, { argument := 2427564373521109984288960413696, coefficient := (-2427564373521109984288960413696) }, { argument := 707162254980863098330042859520, coefficient := (-707162254980863098330042859520) }, { argument := 95268412240135932356870537216, coefficient := (-95268412240135932356870537216) }, { argument := 225946346739381044894498816, coefficient := (-225946346739381044894498816) }, { argument := 95268412240135932356870537216, coefficient := (-95268412240135932356870537216) }, { argument := 228165858986329778144935936, coefficient := (-228165858986329778144935936) }, { argument := 207338267442002829540065280, coefficient := (-207338267442002829540065280) }, { argument := 33100972411563598236572712960, coefficient := (-33100972411563598236572712960) }, { argument := 330297927395813123039806095360, coefficient := (-330297927395813123039806095360) }, { argument := 33100972411563598236572712960, coefficient := (-33100972411563598236572712960) }, { argument := 207314609492728297040117760, coefficient := (-207314609492728297040117760) }, { argument := 176710931108710285270610608128, coefficient := (-176710931108710285270610608128) }, { argument := 6639483639262162678657943863296, coefficient := (-6639483639262162678657943863296) }, { argument := 6638981481068039267539948142592, coefficient := (-6638981481068039267539948142592) }, { argument := 177213089302833696388606328832, coefficient := (-177213089302833696388606328832) }, { argument := 1276143379678109269400192286720, coefficient := (-1276143379678109269400192286720) }, { argument := 4380777087848439856705365344256, coefficient := (-4380777087848439856705365344256) }, { argument := 1276143379678109269400192286720, coefficient := (-1276143379678109269400192286720) }, { argument := 97700024680052204152194859008, coefficient := (-97700024680052204152194859008) }, { argument := 3670840911475125195509078163456, coefficient := (-3670840911475125195509078163456) }, { argument := 3670563278010962380935672102912, coefficient := (-3670563278010962380935672102912) }, { argument := 97977658144215018725600919552, coefficient := (-97977658144215018725600919552) }, { argument := 19922467666185005218470517800960, coefficient := (-19922467666185005218470517800960) }, { argument := 68390348040232650247037264068608, coefficient := (-68390348040232650247037264068608) }, { argument := 19922467666185005218470517800960, coefficient := (-19922467666185005218470517800960) }, { argument := 4451214295998399570237546561536, coefficient := (-4451214295998399570237546561536) }, { argument := 2668089839156520849286103040, coefficient := (-2668089839156520849286103040) }, { argument := 4451214295998399570237546561536, coefficient := (-4451214295998399570237546561536) }, { argument := 2694298973136447380222115840, coefficient := (-2694298973136447380222115840) }, { argument := 780316971013366177467633500160, coefficient := (-780316971013366177467633500160) }, { argument := 2678691722506052396456783904768, coefficient := (-2678691722506052396456783904768) }, { argument := 780316971013366177467633500160, coefficient := (-780316971013366177467633500160) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4031889696321655055996088980865024)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8053735, 19851, 8053735, 10023, 1503, 689558142549369,
    3080250609, 11857174440515919, 76219818261, 2424878139, 23714284970587521, 1245207693,
    1245207693, 42140449821, 2293803645, 76219818261, 42140449821, 86203098389325,
    2424878139, 2293803645, 3080250609, 2667296782363677, 431986945, 140964161,
    1135728922983407, 1423283303, 2667296676463723, 2851113837, 1277771911, 431986945,
    140964161, 260007184470497, 17815, 259999321386527, 8995, 134834653485,
    231431894739, 134834653485, 942581291, 282495, 942581291, 142635,
    2523, 2845445, 2545, 2845445, 1285, 2421,
    1833867, 292771719, 11685685941, 292771719, 7334631, 609530859,
    22901640213, 45799816227, 1222525917, 4406361225, 7563133815, 4406361225,
    576583245, 21663713715, 43324150485, 1156443435
  ]
def negativeCoefficients : Array ℕ := #[
    1217046023229253187044030545920, 5999596611292500936773074944, 1217046023229253187044030545920, 6058531744998714109040001024, 29072248110092602393334120448, 194093362114726849441708376064,
    7102574333388873406787616768, 6674995798996807774684449865728, 175750935100665101533914857472, 5591388305008262043641315328, 6674977809805982079432341323776, 5742506907846323179955945472,
    5742506907846323179955945472, 97169261624873310650307182592, 5289151099332139771012055040, 175750935100665101533914857472, 97169261624873310650307182592, 194112120892173136961313177600,
    5591388305008262043641315328, 5289151099332139771012055040, 7102574333388873406787616768, 6006218397569789352113545936896, 31875010470394576079662612480, 1300164900766094550617817088,
    20459473417367866061755397439488, 26254942834825006086669467648, 6006218159104292665637212258304, 26296883638075525265721655296, 23570731426791778627329458176, 31875010470394576079662612480,
    1300164900766094550617817088, 2341936518189964207044400513024, 168257917784645458963988480, 2341865693825889657203703414784, 169910746053649834788782080, 1243630172552552345339040890880,
    4269164932744021006852999348224, 1243630172552552345339040890880, 4451214295998399570237546561536, 2668089839156520849286103040, 4451214295998399570237546561536, 2694298973136447380222115840,
    48801917486203350524538912768, 107497872774792141000681717760, 192294763182451953101701120, 107497872774792141000681717760, 194183709775599811187179520, 46828950548592275711418433536,
    8457218803555378573344768, 1350171243103252033333886976, 13472678617460798439781564416, 1350171243103252033333886976, 8456253808256022642425856, 5621929880500671156502659072,
    211230347938693051685592367104, 211214372140599701546842718208, 5637905678594021295252307968, 40641508906946155076439244800, 139515193880523562315457495040, 40641508906946155076439244800,
    5318041778851986229124136960, 199812491293358292135019806720, 199797379051918636598364733440, 5333154020291641765779210240
  ]
def negativeScales : Array ℕ := #[
    22, 14, 22, 13, 10, 49,
    31, 53, 36, 31, 54, 30,
    30, 35, 31, 36, 35, 46,
    31, 31, 31, 51, 28, 27,
    50, 30, 51, 31, 30, 28,
    27, 47, 14, 47, 13, 36,
    37, 36, 29, 18, 29, 17,
    11, 21, 11, 21, 10, 11,
    20, 28, 33, 28, 22, 29,
    34, 35, 30, 32, 32, 32,
    29, 34, 35, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22941226580950274, 14276924064937944, 22941226580950274, 13291026768056127, 10553629293917849, 49292665531258974,
    31520400587261890, 53396609775440787, 36149447117056943, 31175265101212674, 54396605887355738, 30213739249027310,
    30213739249027310, 35294486662911672, 31095094752528691, 36149447117056943, 35294486662911672, 46292804958425259,
    31175265101212674, 31095094752528691, 31520400587261890, 51244299781616222, 28686412472770720, 27070753174774239,
    50012539955216675, 30406575711319991, 51244299724336754, 31408878497189412, 30250983184608290, 28686412472770720,
    27070753174774239, 47885544819873177, 14120804863020662, 47885501189523100, 13134907566138845, 36972400386179081,
    37751796746862514, 36972400386179081, 29812041805959772, 18107865807313164, 29812041805959772, 17121968510431347,
    11300924490976301, 21440222863012249, 11313449940963058, 21440222863012249, 10327552644081241, 11241387363998937,
    20806457582277085, 28125200958796615, 33444023370596794, 28125200958796615, 22806292956834750, 29183124021780773,
    34414731876559219, 35414622758354640, 30187217903974440, 32036940623231739, 32816336999721460, 32036940623231739,
    29102953673096789, 34334561527875224, 35334452409670645, 30107047555290456
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
noncomputable def negativeCeiling : ℝ := 39049351421 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1217046023229253187044030545920, coefficient := (-1217046023229253187044030545920) }, { argument := 5999596611292500936773074944, coefficient := (-5999596611292500936773074944) }, { argument := 1217046023229253187044030545920, coefficient := (-1217046023229253187044030545920) }, { argument := 6058531744998714109040001024, coefficient := (-6058531744998714109040001024) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 194093362114726849441708376064, coefficient := (-194093362114726849441708376064) }, { argument := 7102574333388873406787616768, coefficient := (-7102574333388873406787616768) }, { argument := 6674995798996807774684449865728, coefficient := (-6674995798996807774684449865728) }, { argument := 175750935100665101533914857472, coefficient := (-175750935100665101533914857472) }, { argument := 5591388305008262043641315328, coefficient := (-5591388305008262043641315328) }, { argument := 6674977809805982079432341323776, coefficient := (-6674977809805982079432341323776) }, { argument := 5742506907846323179955945472, coefficient := (-5742506907846323179955945472) }, { argument := 5742506907846323179955945472, coefficient := (-5742506907846323179955945472) }, { argument := 97169261624873310650307182592, coefficient := (-97169261624873310650307182592) }, { argument := 5289151099332139771012055040, coefficient := (-5289151099332139771012055040) }, { argument := 175750935100665101533914857472, coefficient := (-175750935100665101533914857472) }, { argument := 97169261624873310650307182592, coefficient := (-97169261624873310650307182592) }, { argument := 194112120892173136961313177600, coefficient := (-194112120892173136961313177600) }, { argument := 5591388305008262043641315328, coefficient := (-5591388305008262043641315328) }, { argument := 5289151099332139771012055040, coefficient := (-5289151099332139771012055040) }, { argument := 7102574333388873406787616768, coefficient := (-7102574333388873406787616768) }, { argument := 6006218397569789352113545936896, coefficient := (-6006218397569789352113545936896) }, { argument := 31875010470394576079662612480, coefficient := (-31875010470394576079662612480) }, { argument := 1300164900766094550617817088, coefficient := (-1300164900766094550617817088) }, { argument := 20459473417367866061755397439488, coefficient := (-20459473417367866061755397439488) }, { argument := 26254942834825006086669467648, coefficient := (-26254942834825006086669467648) }, { argument := 6006218159104292665637212258304, coefficient := (-6006218159104292665637212258304) }, { argument := 26296883638075525265721655296, coefficient := (-26296883638075525265721655296) }, { argument := 23570731426791778627329458176, coefficient := (-23570731426791778627329458176) }, { argument := 31875010470394576079662612480, coefficient := (-31875010470394576079662612480) }, { argument := 1300164900766094550617817088, coefficient := (-1300164900766094550617817088) }, { argument := 2341936518189964207044400513024, coefficient := (-2341936518189964207044400513024) }, { argument := 168257917784645458963988480, coefficient := (-168257917784645458963988480) }, { argument := 2341865693825889657203703414784, coefficient := (-2341865693825889657203703414784) }, { argument := 169910746053649834788782080, coefficient := (-169910746053649834788782080) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 4269164932744021006852999348224, coefficient := (-4269164932744021006852999348224) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 4451214295998399570237546561536, coefficient := (-4451214295998399570237546561536) }, { argument := 2668089839156520849286103040, coefficient := (-2668089839156520849286103040) }, { argument := 4451214295998399570237546561536, coefficient := (-4451214295998399570237546561536) }, { argument := 2694298973136447380222115840, coefficient := (-2694298973136447380222115840) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 107497872774792141000681717760, coefficient := (-107497872774792141000681717760) }, { argument := 192294763182451953101701120, coefficient := (-192294763182451953101701120) }, { argument := 107497872774792141000681717760, coefficient := (-107497872774792141000681717760) }, { argument := 194183709775599811187179520, coefficient := (-194183709775599811187179520) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 5621929880500671156502659072, coefficient := (-5621929880500671156502659072) }, { argument := 211230347938693051685592367104, coefficient := (-211230347938693051685592367104) }, { argument := 211214372140599701546842718208, coefficient := (-211214372140599701546842718208) }, { argument := 5637905678594021295252307968, coefficient := (-5637905678594021295252307968) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 139515193880523562315457495040, coefficient := (-139515193880523562315457495040) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 5318041778851986229124136960, coefficient := (-5318041778851986229124136960) }, { argument := 199812491293358292135019806720, coefficient := (-199812491293358292135019806720) }, { argument := 199797379051918636598364733440, coefficient := (-199797379051918636598364733440) }, { argument := 5333154020291641765779210240, coefficient := (-5333154020291641765779210240) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
