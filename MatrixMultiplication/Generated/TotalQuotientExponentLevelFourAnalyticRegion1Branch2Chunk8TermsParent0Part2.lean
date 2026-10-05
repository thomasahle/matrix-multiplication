import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 72459359056823393720866074062225408
def positiveArguments : Array ℕ := #[
    1755, 59, 21416348781, 2545, 21415965587, 1285,
    547839013, 13395, 4371, 59780428619, 44133, 17530847253,
    88407, 39621, 13395, 4371, 323613715, 8507,
    20397895813, 210503, 6697, 20397883281, 3439, 3439,
    116383, 6335, 210503, 116383, 161810929, 6697,
    6335, 8507, 12552377, 1173922743, 235773, 3598360055
  ]
def positiveCoefficients : Array ℕ := #[
    1112363401700271299813357062717440, 4674461588341595918019093069824, 101135847668840583654240814104576, 196909837498830799976141946880, 101134038086338546903412797079552, 198844118810214206655671828480,
    165574181951973621858009006211072, 2072775853278458597784221122560, 84547436120568705962251124736, 564610184883893823958417458331648, 1707312742305677739753845293056, 165574170967749182703214239154176,
    1710040078954728343171982426112, 1532763196766439120993068777472, 2072775853278458597784221122560, 84547436120568705962251124736, 12225780488903437986689051525120, 1316394489275091249820856221696,
    385305358033513089316980514619392, 32573761511211300500886293315584, 1036310555386773962624929366016, 385305121310726036027405242466304, 1064318948775605691344522051584, 1064318948775605691344522051584,
    18009396949018801566698096820224, 980293768609110505185743994880, 32573761511211300500886293315584, 18009396949018801566698096820224, 12226088122745598046856852537344, 1036310555386773962624929366016,
    980293768609110505185743994880, 1316394489275091249820856221696, 237107697700575314314231021568, 11087386830043192841397658976256, 4560513076287999430527987744768, 67971099668115892435942501253120
  ]
def positiveScales : Array ℕ := #[
    10, 5, 34, 11, 34, 10,
    29, 13, 12, 35, 15, 34,
    16, 15, 13, 12, 28, 13,
    34, 17, 12, 34, 11, 11,
    16, 12, 17, 16, 27, 12,
    12, 13, 23, 30, 17, 31
  ]
def negativeArguments : Array ℕ := #[
    8371458235, 4877299525, 1149, 1149, 805, 1915,
    1915, 345, 6549516505, 11241672487, 6549516505, 29491,
    29491, 805, 33321, 33321, 9085, 345,
    104603568781149, 22301835, 104602685094051, 11260455, 498735, 713,
    59, 1279, 11423, 11423
  ]
def negativeCoefficients : Array ℕ := #[
    308852295169586545747841515520, 89970296108500161084679782400, 711196552569450967929546866688, 711196552569450967929546866688, 15570964556636423770215546880, 37041487112992237912997232640,
    37041487112992237912997232640, 13346541048545506088756183040, 120817254774271644885141422080, 414744510656301932861387177984, 120817254774271644885141422080, 1140877803080160927720314765312,
    1140877803080160927720314765312, 15570964556636423770215546880, 644521875766064939686151847936, 644521875766064939686151847936, 175729457139182496835289743360, 13346541048545506088756183040,
    58886574173050835606320447488, 51424530327387282258001920, 58886076701440177491947814912, 51929682884630772260536320, 18841675582671940045221396480, 13791425750163689625048055808,
    4674461588341595918019093069824, 202665639711488175564285424959488, 905023300400441528331052544688128, 905023300400441528331052544688128
  ]
def negativeScales : Array ℕ := #[
    32, 32, 10, 10, 9, 10,
    10, 8, 32, 33, 32, 14,
    14, 9, 15, 15, 13, 8,
    46, 24, 46, 23, 18, 9,
    5, 10, 13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10777255315166917, 5882643049164642, 34317993488506680, 11313449940963057, 34317967674721379, 10327552644081240,
    29029176766758700, 13709406960724143, 12093747662785668, 35798954189849927, 15429570199331410, 34029176671050019,
    16431872985200830, 15273977672619719, 13709406960724143, 12093747662785668, 28269697510696192, 13054434738760842,
    34247701284564434, 17683481268553390, 12709299252706570, 34247700398205372, 11747773400513505, 11747773400513505,
    16828520814340383, 12629128904027399, 17683481268553390, 16828520814340383, 27269733812365039, 12709299252706570,
    12629128904027399, 13054434738760842, 23581457252402967, 30128690320391395, 17847038989106135, 31744692405091809
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32962831816468606, 32183435427951812, 10166163082646114, 10166163082646114, 9652844973024881, 10903128681431424,
    10903128681431424, 8430452551665554, 32608741262691672, 33388137638276099, 32608741262691672, 14847987124286611,
    14847987124286611, 9652844973024881, 15024144077773686, 15024144077773686, 13149270799121479, 8430452551665554,
    46571925401569136, 24410659084513403, 46571913213683062, 23424761787631594, 18927913932938771, 9477758266444015,
    5882643052550791, 10320800548881638, 13479653972171065, 13479653972171065
  ]

abbrev PositiveTerm := Fin 36
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 978247065159 / 1000000000000
noncomputable def negativeCeiling : ℝ := 6410963419 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 308852295169586545747841515520, coefficient := (-308852295169586545747841515520) }, { argument := 89970296108500161084679782400, coefficient := (-89970296108500161084679782400) }, { argument := 711196552569450967929546866688, coefficient := (-711196552569450967929546866688) }, { argument := 711196552569450967929546866688, coefficient := (-711196552569450967929546866688) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 37041487112992237912997232640, coefficient := (-37041487112992237912997232640) }, { argument := 13346541048545506088756183040, coefficient := (-13346541048545506088756183040) }, { argument := 120817254774271644885141422080, coefficient := (-120817254774271644885141422080) }, { argument := 414744510656301932861387177984, coefficient := (-414744510656301932861387177984) }, { argument := 120817254774271644885141422080, coefficient := (-120817254774271644885141422080) }, { argument := 1140877803080160927720314765312, coefficient := (-1140877803080160927720314765312) }, { argument := 1140877803080160927720314765312, coefficient := (-1140877803080160927720314765312) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 644521875766064939686151847936, coefficient := (-644521875766064939686151847936) }, { argument := 644521875766064939686151847936, coefficient := (-644521875766064939686151847936) }, { argument := 175729457139182496835289743360, coefficient := (-175729457139182496835289743360) }, { argument := 13346541048545506088756183040, coefficient := (-13346541048545506088756183040) }, { argument := 58886574173050835606320447488, coefficient := (-58886574173050835606320447488) }, { argument := 51424530327387282258001920, coefficient := (-51424530327387282258001920) }, { argument := 58886076701440177491947814912, coefficient := (-58886076701440177491947814912) }, { argument := 51929682884630772260536320, coefficient := (-51929682884630772260536320) }, { argument := 18841675582671940045221396480, coefficient := (-18841675582671940045221396480) }, { argument := 13791425750163689625048055808, coefficient := (-13791425750163689625048055808) }, { argument := 1112363401700271299813357062717440, coefficient := 1112363401700271299813357062717440 }, { argument := 4674461588341595918019093069824, coefficient := 4674461588341595918019093069824 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 101135847668840583654240814104576, coefficient := 101135847668840583654240814104576 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 101134038086338546903412797079552, coefficient := 101134038086338546903412797079552 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 202665639711488175564285424959488, coefficient := (-202665639711488175564285424959488) }, { argument := 165574181951973621858009006211072, coefficient := 165574181951973621858009006211072 }, { argument := 2072775853278458597784221122560, coefficient := 2072775853278458597784221122560 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 564610184883893823958417458331648, coefficient := 564610184883893823958417458331648 }, { argument := 1707312742305677739753845293056, coefficient := 1707312742305677739753845293056 }, { argument := 165574170967749182703214239154176, coefficient := 165574170967749182703214239154176 }, { argument := 1710040078954728343171982426112, coefficient := 1710040078954728343171982426112 }, { argument := 1532763196766439120993068777472, coefficient := 1532763196766439120993068777472 }, { argument := 2072775853278458597784221122560, coefficient := 2072775853278458597784221122560 }, { argument := 84547436120568705962251124736, coefficient := 84547436120568705962251124736 }, { argument := 905023300400441528331052544688128, coefficient := (-905023300400441528331052544688128) }, { argument := 12225780488903437986689051525120, coefficient := 12225780488903437986689051525120 }, { argument := 1316394489275091249820856221696, coefficient := 1316394489275091249820856221696 }, { argument := 385305358033513089316980514619392, coefficient := 385305358033513089316980514619392 }, { argument := 32573761511211300500886293315584, coefficient := 32573761511211300500886293315584 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 385305121310726036027405242466304, coefficient := 385305121310726036027405242466304 }, { argument := 1064318948775605691344522051584, coefficient := 1064318948775605691344522051584 }, { argument := 1064318948775605691344522051584, coefficient := 1064318948775605691344522051584 }, { argument := 18009396949018801566698096820224, coefficient := 18009396949018801566698096820224 }, { argument := 980293768609110505185743994880, coefficient := 980293768609110505185743994880 }, { argument := 32573761511211300500886293315584, coefficient := 32573761511211300500886293315584 }, { argument := 18009396949018801566698096820224, coefficient := 18009396949018801566698096820224 }, { argument := 12226088122745598046856852537344, coefficient := 12226088122745598046856852537344 }, { argument := 1036310555386773962624929366016, coefficient := 1036310555386773962624929366016 }, { argument := 980293768609110505185743994880, coefficient := 980293768609110505185743994880 }, { argument := 1316394489275091249820856221696, coefficient := 1316394489275091249820856221696 }, { argument := 905023300400441528331052544688128, coefficient := (-905023300400441528331052544688128) }, { argument := 237107697700575314314231021568, coefficient := 237107697700575314314231021568 }, { argument := 11087386830043192841397658976256, coefficient := 11087386830043192841397658976256 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 67971099668115892435942501253120, coefficient := 67971099668115892435942501253120 }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9813659399154851395991673539395584)
def positiveArguments : Array ℕ := #[
    241937, 7705, 235773, 134067, 241937, 3776991,
    4623, 293480799, 235773, 7705, 4623, 7705,
    118657, 134067, 25104749, 489777, 7668175, 1575,
    1395, 65295, 17775, 7668177, 65295, 1575,
    1575, 675, 1575, 17775, 675, 489775,
    1395
  ]
def positiveCoefficients : Array ℕ := #[
    4679742176321672618254209646592, 149036375042091484657777377280, 4560513076287999430527987744768, 2593232925732391833045326364672, 4679742176321672618254209646592, 73057631045633245779242470342656,
    2861498400808156505429325643776, 11087391108507226321296222584832, 4560513076287999430527987744768, 149036375042091484657777377280, 2861498400808156505429325643776, 149036375042091484657777377280,
    4590320351296417727459543220224, 2593232925732391833045326364672, 237107650476910485617778884608, 37006503822087139581254172672, 579390921676463066984533196800, 30464930654288655202595635200,
    26983224293798523179441848320, 1262988982267795391399036190720, 343818503098400537286436454400, 579391072792190518813180035072, 1262988982267795391399036190720, 30464930654288655202595635200,
    30464930654288655202595635200, 26112797703675990173653401600, 30464930654288655202595635200, 343818503098400537286436454400, 26112797703675990173653401600, 37006352706359687752607334400,
    26983224293798523179441848320
  ]
def positiveScales : Array ℕ := #[
    17, 12, 17, 17, 17, 21,
    12, 28, 17, 12, 12, 12,
    16, 17, 24, 18, 22, 10,
    10, 15, 14, 22, 15, 10,
    10, 9, 10, 14, 9, 18,
    10
  ]
def negativeArguments : Array ℕ := #[
    1279, 59
  ]
def negativeCoefficients : Array ℕ := #[
    202665639711488175564285424959488, 4674461588341595918019093069824
  ]
def negativeScales : Array ℕ := #[
    10, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    17884271895203256, 12911579241070476, 17847038989106135, 17032594642363513, 17884271895203256, 21848805915276843,
    12174613647235941, 28128690877106674, 17847038989106135, 12911579241070476, 12174613647235941, 12911579241070476,
    16856437687088554, 17032594642363513, 24581456965067910, 18901765500479340, 22870451831153324, 10621136113274016,
    10446049406716546, 15994684899055573, 14117561939394139, 22870452207434473, 15994684899055573, 10621136113274016,
    10621136113274016, 9398743691938192, 10621136113274016, 14117561939394139, 9398743691938192, 18901759609235042,
    10446049406716546
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10320800548881638, 5882643052550791
  ]

abbrev PositiveTerm := Fin 31
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 3088250817 / 100000000000
noncomputable def negativeCeiling : ℝ := 25508579011 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4679742176321672618254209646592, coefficient := 4679742176321672618254209646592 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 2593232925732391833045326364672, coefficient := 2593232925732391833045326364672 }, { argument := 4679742176321672618254209646592, coefficient := 4679742176321672618254209646592 }, { argument := 73057631045633245779242470342656, coefficient := 73057631045633245779242470342656 }, { argument := 2861498400808156505429325643776, coefficient := 2861498400808156505429325643776 }, { argument := 11087391108507226321296222584832, coefficient := 11087391108507226321296222584832 }, { argument := 4560513076287999430527987744768, coefficient := 4560513076287999430527987744768 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 2861498400808156505429325643776, coefficient := 2861498400808156505429325643776 }, { argument := 149036375042091484657777377280, coefficient := 149036375042091484657777377280 }, { argument := 4590320351296417727459543220224, coefficient := 4590320351296417727459543220224 }, { argument := 2593232925732391833045326364672, coefficient := 2593232925732391833045326364672 }, { argument := 237107650476910485617778884608, coefficient := 237107650476910485617778884608 }, { argument := 202665639711488175564285424959488, coefficient := (-202665639711488175564285424959488) }, { argument := 37006503822087139581254172672, coefficient := 37006503822087139581254172672 }, { argument := 579390921676463066984533196800, coefficient := 579390921676463066984533196800 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 26983224293798523179441848320, coefficient := 26983224293798523179441848320 }, { argument := 1262988982267795391399036190720, coefficient := 1262988982267795391399036190720 }, { argument := 343818503098400537286436454400, coefficient := 343818503098400537286436454400 }, { argument := 579391072792190518813180035072, coefficient := 579391072792190518813180035072 }, { argument := 1262988982267795391399036190720, coefficient := 1262988982267795391399036190720 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 26112797703675990173653401600, coefficient := 26112797703675990173653401600 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 343818503098400537286436454400, coefficient := 343818503098400537286436454400 }, { argument := 26112797703675990173653401600, coefficient := 26112797703675990173653401600 }, { argument := 37006352706359687752607334400, coefficient := 37006352706359687752607334400 }, { argument := 26983224293798523179441848320, coefficient := 26983224293798523179441848320 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
