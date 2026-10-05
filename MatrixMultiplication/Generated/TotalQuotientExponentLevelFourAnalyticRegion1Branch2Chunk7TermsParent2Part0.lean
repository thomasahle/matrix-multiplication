import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2476363691802365739446366038392832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    535, 489, 535, 489, 1819659, 7515,
    13411829, 12105, 375, 12105, 8085, 1835019,
    7515, 45, 187655282446085, 5242356135866619, 1932243155, 1711484239,
    80098713755, 21811485371, 2621178795593739, 80098713755, 1932243155, 1932237203,
    828118239, 1932237203, 21811485371, 828118239, 93826913562613, 1711484239,
    12825, 9975, 1425, 13395, 158175, 11115,
    9975, 158175, 1425, 11115, 11115, 11115,
    11115, 11115, 12825, 13395, 559822088913, 406673508733845,
    15996392811, 3966489271383895, 16414599159, 522757935, 15996392811, 9095988069,
    16414599159, 256255939737, 313654761, 101668423776257, 15996392811, 522757935,
    313654761, 522757935, 8050472199, 9095988069
  ]
def negativeCoefficients : Array ℕ := #[
    20696810031802451470969733120, 18917271225329717325802242048, 20696810031802451470969733120, 18917271225329717325802242048, 34372386687408382959635398656, 145361240550463011966670602240,
    506684573948632887174073679872, 234144752742961378557092167680, 7253554917687775048237056000, 234144752742961378557092167680, 156386644025348430039990927360, 34662528884115893961564880896,
    145361240550463011966670602240, 6963412720980264046307573760, 211281065024573396283859927040, 5902368285008084657266287968256, 142574379873848386272540753920, 126285246972082207418163920896,
    5910241893087215983597526712320, 1609403554025187323101413638144, 5902369923553704231493825462272, 5910241893087215983597526712320, 142574379873848386272540753920, 142573940693765479395535880192,
    122208681740832320653772193792, 142573940693765479395535880192, 1609403554025187323101413638144, 122208681740832320653772193792, 211279426478953822056322433024, 126285246972082207418163920896,
    484514801142425598925209600, 376844845332997688052940800, 430679823237711643489075200, 506048792304311181099663360, 5975682547423249053410918400, 13437210485016603276859146240,
    376844845332997688052940800, 5975682547423249053410918400, 430679823237711643489075200, 419912827656768852401848320, 419912827656768852401848320, 419912827656768852401848320,
    13437210485016603276859146240, 419912827656768852401848320, 484514801142425598925209600, 506048792304311181099663360, 10084858204089437920419643392, 915747331197598246283834818560,
    73770341071761081393053958144, 8931739802286789852448906280960, 75698977439650259991565172736, 2410795459861473248139018240, 73770341071761081393053958144, 41947841001589634517618917376,
    75698977439650259991565172736, 1181771934424094186237746741248, 46287272829340286364269150208, 915747750868193401983094226944, 73770341071761081393053958144, 2410795459861473248139018240,
    46287272829340286364269150208, 2410795459861473248139018240, 74252500163733376042681761792, 41947841001589634517618917376
  ]
def negativeScales : Array ℕ := #[
    9, 8, 9, 8, 20, 12,
    23, 13, 8, 13, 12, 20,
    12, 5, 47, 52, 30, 30,
    36, 34, 51, 36, 30, 30,
    29, 30, 34, 29, 46, 30,
    13, 13, 10, 13, 17, 13,
    13, 17, 10, 13, 13, 13,
    13, 13, 13, 13, 39, 48,
    33, 51, 33, 28, 33, 33,
    33, 37, 28, 46, 33, 28,
    28, 28, 32, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9063395081288510, 8933690662845865, 9063395081288510, 8933690662845865, 20795236687860544, 12875557391602924,
    23677002658341279, 13563315458888280, 8550746785384604, 13563315458888280, 12981032075801390, 20807363571052247,
    12875557391602924, 5491853096329881, 47415078230699696, 52219136788803567, 30847629511119346, 30672600860703224,
    36221060024539044, 34344368970315217, 51219137189307432, 36221060024539044, 30847629511119346, 30847625067095643,
    29625261530023625, 30847625067095643, 34344368970315217, 29625261530023625, 46415067042140012, 30672600860703224,
    13646671205401350, 13284101125997071, 10476746203939589, 13709406960819918, 17271162070289573, 13440220327914385,
    13284101125997071, 17271162070289573, 10476746203939589, 13440220327914385, 13440220327914385, 13440220327914385,
    13440220327914385, 13440220327914385, 13646671205401350, 13709406960819918, 39026177456246190, 48530864343165104,
    33897027566851975, 51816784070987198, 33934260476881809, 28961567827562181, 33897027566851975, 33082583215867498,
    33934260476881809, 37898794493159772, 28224602220739925, 46530865004326242, 33897027566851975, 28961567827562181,
    28224602220739925, 28961567827562181, 32906426265612401, 33082583215867498
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
noncomputable def negativeCeiling : ℝ := 4440158631 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 34372386687408382959635398656, coefficient := (-34372386687408382959635398656) }, { argument := 145361240550463011966670602240, coefficient := (-145361240550463011966670602240) }, { argument := 506684573948632887174073679872, coefficient := (-506684573948632887174073679872) }, { argument := 234144752742961378557092167680, coefficient := (-234144752742961378557092167680) }, { argument := 7253554917687775048237056000, coefficient := (-7253554917687775048237056000) }, { argument := 234144752742961378557092167680, coefficient := (-234144752742961378557092167680) }, { argument := 156386644025348430039990927360, coefficient := (-156386644025348430039990927360) }, { argument := 34662528884115893961564880896, coefficient := (-34662528884115893961564880896) }, { argument := 145361240550463011966670602240, coefficient := (-145361240550463011966670602240) }, { argument := 6963412720980264046307573760, coefficient := (-6963412720980264046307573760) }, { argument := 211281065024573396283859927040, coefficient := (-211281065024573396283859927040) }, { argument := 5902368285008084657266287968256, coefficient := (-5902368285008084657266287968256) }, { argument := 142574379873848386272540753920, coefficient := (-142574379873848386272540753920) }, { argument := 126285246972082207418163920896, coefficient := (-126285246972082207418163920896) }, { argument := 5910241893087215983597526712320, coefficient := (-5910241893087215983597526712320) }, { argument := 1609403554025187323101413638144, coefficient := (-1609403554025187323101413638144) }, { argument := 5902369923553704231493825462272, coefficient := (-5902369923553704231493825462272) }, { argument := 5910241893087215983597526712320, coefficient := (-5910241893087215983597526712320) }, { argument := 142574379873848386272540753920, coefficient := (-142574379873848386272540753920) }, { argument := 142573940693765479395535880192, coefficient := (-142573940693765479395535880192) }, { argument := 122208681740832320653772193792, coefficient := (-122208681740832320653772193792) }, { argument := 142573940693765479395535880192, coefficient := (-142573940693765479395535880192) }, { argument := 1609403554025187323101413638144, coefficient := (-1609403554025187323101413638144) }, { argument := 122208681740832320653772193792, coefficient := (-122208681740832320653772193792) }, { argument := 211279426478953822056322433024, coefficient := (-211279426478953822056322433024) }, { argument := 126285246972082207418163920896, coefficient := (-126285246972082207418163920896) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 10084858204089437920419643392, coefficient := (-10084858204089437920419643392) }, { argument := 915747331197598246283834818560, coefficient := (-915747331197598246283834818560) }, { argument := 73770341071761081393053958144, coefficient := (-73770341071761081393053958144) }, { argument := 8931739802286789852448906280960, coefficient := (-8931739802286789852448906280960) }, { argument := 75698977439650259991565172736, coefficient := (-75698977439650259991565172736) }, { argument := 2410795459861473248139018240, coefficient := (-2410795459861473248139018240) }, { argument := 73770341071761081393053958144, coefficient := (-73770341071761081393053958144) }, { argument := 41947841001589634517618917376, coefficient := (-41947841001589634517618917376) }, { argument := 75698977439650259991565172736, coefficient := (-75698977439650259991565172736) }, { argument := 1181771934424094186237746741248, coefficient := (-1181771934424094186237746741248) }, { argument := 46287272829340286364269150208, coefficient := (-46287272829340286364269150208) }, { argument := 915747750868193401983094226944, coefficient := (-915747750868193401983094226944) }, { argument := 73770341071761081393053958144, coefficient := (-73770341071761081393053958144) }, { argument := 2410795459861473248139018240, coefficient := (-2410795459861473248139018240) }, { argument := 46287272829340286364269150208, coefficient := (-46287272829340286364269150208) }, { argument := 2410795459861473248139018240, coefficient := (-2410795459861473248139018240) }, { argument := 74252500163733376042681761792, coefficient := (-74252500163733376042681761792) }, { argument := 41947841001589634517618917376, coefficient := (-41947841001589634517618917376) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5974510114316249795755503198928896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    559821443793, 4185, 3255, 465, 4371, 51615,
    3627, 3255, 51615, 465, 3627, 3627,
    3627, 3627, 3627, 4185, 4371, 10812585,
    1726198845, 68899474455, 1726198845, 43245405, 17841659234107, 10606631,
    321517554706807, 262457699, 8349901, 1286041539004377, 4287787, 4287787,
    145107739, 7898555, 262457699, 145107739, 35712054428629, 8349901,
    7898555, 10606631, 1819659, 7515, 13411829, 12105,
    375, 12105, 8085, 1835019, 7515, 45,
    642086793625101, 17795218981143027, 3318563885, 2940007057, 137510708933, 37501075781,
    8897611954827717, 137510708933, 3318563885, 3318502733, 1422385809, 3318502733,
    37501075781, 1422385809, 321040932556347, 2940007057
  ]
def negativeCoefficients : Array ℕ := #[
    10084846582640671483402125312, 19763103730809465219317760, 15371302901740695170580480, 17567203316275080194949120, 20641463896623219229065216, 243744946013316737704919040,
    548096743467782502082412544, 15371302901740695170580480, 243744946013316737704919040, 17567203316275080194949120, 17128023233368203190075392, 17128023233368203190075392,
    17128023233368203190075392, 548096743467782502082412544, 17128023233368203190075392, 19763103730809465219317760, 20641463896623219229065216, 99728494135115396079943680,
    15921374157024011432503541760, 158871371510559236082011996160, 15921374157024011432503541760, 99717114799864926500290560, 10043961234799456782211088384, 97828903770637007583182848,
    361996584892662266877410541568, 2420745001813847655728545792, 77014243393905729373995008, 361988512240193215912646541312, 79095709431578857194913792, 79095709431578857194913792,
    1338382662223821188850778112, 72851311318559473732157440, 2420745001813847655728545792, 1338382662223821188850778112, 10052049688588027239935770624, 77014243393905729373995008,
    72851311318559473732157440, 97828903770637007583182848, 34372386687408382959635398656, 145361240550463011966670602240, 506684573948632887174073679872, 234144752742961378557092167680,
    7253554917687775048237056000, 234144752742961378557092167680, 156386644025348430039990927360, 34662528884115893961564880896, 145361240550463011966670602240, 6963412720980264046307573760,
    722925461127380357532063105024, 20035635393113028470622123982848, 489733589430802367779207905280, 433868462043032079354766032896, 20292998840651334798797726285824, 5534181979367156359481176096768,
    20035640942124688384638704418816, 20292998840651334798797726285824, 489733589430802367779207905280, 489724564988453603887204532224, 419814191883189059301622677504, 489724564988453603887204532224,
    5534181979367156359481176096768, 419814191883189059301622677504, 722919912115720443515482669056, 433868462043032079354766032896
  ]
def negativeScales : Array ℕ := #[
    39, 12, 11, 8, 12, 15,
    11, 11, 15, 8, 11, 11,
    11, 11, 11, 12, 12, 23,
    30, 36, 30, 25, 44, 23,
    48, 27, 22, 50, 22, 22,
    27, 22, 27, 27, 45, 22,
    22, 23, 20, 12, 23, 13,
    8, 13, 12, 20, 12, 5,
    49, 53, 31, 31, 37, 35,
    52, 37, 31, 31, 30, 31,
    35, 30, 48, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39026175793732368, 12031011907437707, 11668441828086828, 8861086908132560, 12093747662785669, 15655502772369993,
    11824561031027542, 11668441828086828, 15655502772369993, 8861086908132560, 11824561031027542, 11824561031027542,
    11824561031027542, 11824561031027542, 11824561031027542, 12031011907437707, 12093747662785669, 23366208138333985,
    30684951515640630, 36003773927390173, 30684951515640630, 25366043512894097, 44020315022420994, 23338463147851079,
    48191890838595412, 27967509691614881, 22993327683080818, 50191858665624641, 22031801809617027, 22031801809617027,
    27112549223501389, 22913157318637533, 27967509691614881, 27112549223501389, 45021476364624065, 22993327683080818,
    22913157318637533, 23338463147851079, 20795236687860544, 12875557391602924, 23677002658341279, 13563315458888280,
    8550746785384604, 13563315458888280, 12981032075801390, 20807363571052247, 12875557391602924, 5491853096329881,
    49189761654227180, 53982339222222290, 31627911901525850, 31453172472002608, 37000753019655934, 35126212931192872,
    52982339621786999, 37000753019655934, 31627911901525850, 31627885316381464, 30405665689715230, 31627885316381464,
    35126212931192872, 30405665689715230, 48189750580385189, 31453172472002608
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
noncomputable def negativeCeiling : ℝ := 51618447027 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10084846582640671483402125312, coefficient := (-10084846582640671483402125312) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 99728494135115396079943680, coefficient := (-99728494135115396079943680) }, { argument := 15921374157024011432503541760, coefficient := (-15921374157024011432503541760) }, { argument := 158871371510559236082011996160, coefficient := (-158871371510559236082011996160) }, { argument := 15921374157024011432503541760, coefficient := (-15921374157024011432503541760) }, { argument := 99717114799864926500290560, coefficient := (-99717114799864926500290560) }, { argument := 10043961234799456782211088384, coefficient := (-10043961234799456782211088384) }, { argument := 97828903770637007583182848, coefficient := (-97828903770637007583182848) }, { argument := 361996584892662266877410541568, coefficient := (-361996584892662266877410541568) }, { argument := 2420745001813847655728545792, coefficient := (-2420745001813847655728545792) }, { argument := 77014243393905729373995008, coefficient := (-77014243393905729373995008) }, { argument := 361988512240193215912646541312, coefficient := (-361988512240193215912646541312) }, { argument := 79095709431578857194913792, coefficient := (-79095709431578857194913792) }, { argument := 79095709431578857194913792, coefficient := (-79095709431578857194913792) }, { argument := 1338382662223821188850778112, coefficient := (-1338382662223821188850778112) }, { argument := 72851311318559473732157440, coefficient := (-72851311318559473732157440) }, { argument := 2420745001813847655728545792, coefficient := (-2420745001813847655728545792) }, { argument := 1338382662223821188850778112, coefficient := (-1338382662223821188850778112) }, { argument := 10052049688588027239935770624, coefficient := (-10052049688588027239935770624) }, { argument := 77014243393905729373995008, coefficient := (-77014243393905729373995008) }, { argument := 72851311318559473732157440, coefficient := (-72851311318559473732157440) }, { argument := 97828903770637007583182848, coefficient := (-97828903770637007583182848) }, { argument := 34372386687408382959635398656, coefficient := (-34372386687408382959635398656) }, { argument := 145361240550463011966670602240, coefficient := (-145361240550463011966670602240) }, { argument := 506684573948632887174073679872, coefficient := (-506684573948632887174073679872) }, { argument := 234144752742961378557092167680, coefficient := (-234144752742961378557092167680) }, { argument := 7253554917687775048237056000, coefficient := (-7253554917687775048237056000) }, { argument := 234144752742961378557092167680, coefficient := (-234144752742961378557092167680) }, { argument := 156386644025348430039990927360, coefficient := (-156386644025348430039990927360) }, { argument := 34662528884115893961564880896, coefficient := (-34662528884115893961564880896) }, { argument := 145361240550463011966670602240, coefficient := (-145361240550463011966670602240) }, { argument := 6963412720980264046307573760, coefficient := (-6963412720980264046307573760) }, { argument := 722925461127380357532063105024, coefficient := (-722925461127380357532063105024) }, { argument := 20035635393113028470622123982848, coefficient := (-20035635393113028470622123982848) }, { argument := 489733589430802367779207905280, coefficient := (-489733589430802367779207905280) }, { argument := 433868462043032079354766032896, coefficient := (-433868462043032079354766032896) }, { argument := 20292998840651334798797726285824, coefficient := (-20292998840651334798797726285824) }, { argument := 5534181979367156359481176096768, coefficient := (-5534181979367156359481176096768) }, { argument := 20035640942124688384638704418816, coefficient := (-20035640942124688384638704418816) }, { argument := 20292998840651334798797726285824, coefficient := (-20292998840651334798797726285824) }, { argument := 489733589430802367779207905280, coefficient := (-489733589430802367779207905280) }, { argument := 489724564988453603887204532224, coefficient := (-489724564988453603887204532224) }, { argument := 419814191883189059301622677504, coefficient := (-419814191883189059301622677504) }, { argument := 489724564988453603887204532224, coefficient := (-489724564988453603887204532224) }, { argument := 5534181979367156359481176096768, coefficient := (-5534181979367156359481176096768) }, { argument := 419814191883189059301622677504, coefficient := (-419814191883189059301622677504) }, { argument := 722919912115720443515482669056, coefficient := (-722919912115720443515482669056) }, { argument := 433868462043032079354766032896, coefficient := (-433868462043032079354766032896) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
