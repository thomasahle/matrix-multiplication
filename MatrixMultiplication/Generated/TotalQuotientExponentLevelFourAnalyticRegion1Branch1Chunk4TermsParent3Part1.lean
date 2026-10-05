import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

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
def constantNumerator : ℤ := (-16730857611895999170569996393775104)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21638435, 5564169, 21638435, 1506138550665, 2926138225, 41607554263935,
    19312512285, 954845105, 9640855415, 19620526835, 188619832415, 2926138225,
    954845105, 556951342149267, 16806460579942765, 22774062437, 1846545603, 395776274243,
    715844178763, 16806460583014765, 395776274243, 11694788819, 11694788819, 22774062437,
    22774062437, 715844178763, 22774062437, 556951339077267, 1846545603, 10043822829047,
    196186072035571, 36137140193, 3611650854637245, 1407940527, 2346567545, 71804966877,
    2346567545, 1407940527, 1150287410559, 73682220913, 196186072377011, 71804966877,
    2346567545, 73682220913, 2346567545, 71804966877, 2346567545, 10043822829047,
    41612375, 7298419625, 1824605125, 10402875, 1648515, 1062043785,
    11295282273, 531023493, 1648515, 448419247658681, 3795178205, 4211436801617925,
    42831296885, 3795178205, 8422871657203005, 3795178205
  ]
def negativeCoefficients : Array ℕ := #[
    99789668150149835380490240, 102640801525868402105647104, 99789668150149835380490240, 6783045015543232910422179840, 107955445921747473062376243200, 187383765878855357976815861760,
    89063242885441665276460400640, 4403445820492331138070609920, 88921196246070944917167800320, 90483709279148868869386403840, 6795745655831035221083422720, 107955445921747473062376243200,
    4403445820492331138070609920, 313535732120867060498042978304, 9461196200655895819296891207680, 210053650647010529353029124096, 272502033271797443485010755584, 3650391820703453253351289913344,
    6602497181147925557772239765504, 9461196202385278076207161671680, 3650391820703453253351289913344, 215730776340172976092300181504, 215730776340172976092300181504, 210053650647010529353029124096,
    210053650647010529353029124096, 6602497181147925557772239765504, 210053650647010529353029124096, 313535730391484803587772514304, 272502033271797443485010755584, 180933427001085400593358389248,
    14136696334634861460430526611456, 2666450306784135969242246807552, 130123435545093039978778365788160, 1662202788644656188618543464448, 86573061908575843157215805440, 2649135694402420800610803646464,
    2770337981074426981030905774080, 1662202788644656188618543464448, 42438114947583878315667187826688, 2718394143929281475136576290816, 14136696359238206368740641079296, 2649135694402420800610803646464,
    86573061908575843157215805440, 2718394143929281475136576290816, 86573061908575843157215805440, 2649135694402420800610803646464, 2770337981074426981030905774080, 180933427001085400593358389248,
    95951603990528687865856000, 16829009870614279758020608000, 16829011888226912820002816000, 95949586377895625883648000, 486555748906740823716003840, 156729999175750489511276052480,
    1666889450642714429751866425344, 156730471559972729065473835008, 486555748906740823716003840, 252437594582674239061567209472, 17502170265438850948341432320, 9483312605230440257883104870400,
    197524492995667032131281879040, 17502170265438850948341432320, 9483310414192241359696554885120, 17502170265438850948341432320
  ]
def negativeScales : Array ℕ := #[
    24, 22, 24, 40, 31, 45,
    34, 29, 33, 34, 37, 31,
    29, 48, 53, 34, 30, 38,
    39, 53, 38, 33, 33, 34,
    34, 39, 34, 48, 30, 43,
    47, 35, 51, 30, 31, 36,
    31, 30, 40, 36, 47, 36,
    31, 36, 31, 36, 31, 43,
    25, 32, 30, 23, 20, 29,
    33, 28, 20, 48, 31, 51,
    35, 31, 52, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24367092824217978, 22407734808715331, 24367092824217978, 40453991629218129, 31446350775141421, 45241910721269661,
    34168816799612471, 29830691478389925, 33166514013743051, 34191644729066733, 37456690419787348, 31446350775141421,
    29830691478389925, 48984544639433422, 53899865449305225, 34406672611228839, 30782181746768298, 38525894172928457,
    39380854627073102, 53899865449568931, 38525894172928457, 33445146759043505, 33445146759043505, 34406672611228839,
    34406672611228839, 39380854627073102, 34406672611228839, 48984544631475886, 30782181746768298, 43191373718640710,
    47479215951435706, 35072763288152323, 51681579854761139, 30390939248178582, 31127904842344784, 36063364590150073,
    31127904842344784, 30390939248178582, 40065131516324261, 36100597496349048, 47479215953946556, 36063364590150073,
    31127904842344784, 36100597496349048, 31127904842344784, 36063364590150073, 31127904842344784, 43191373718640710,
    25310509295851609, 32764936955822540, 30764937128785751, 23310478959408832, 20652735583639001, 29984196117868241,
    33395001273501818, 28984200466145881, 20652735583639001, 48671841533244056, 31821520484873869, 51903233944586737,
    35317946309997787, 31821520484873869, 52903233611264331, 31821520484873869
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
noncomputable def negativeCeiling : ℝ := 82209094901 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 102640801525868402105647104, coefficient := (-102640801525868402105647104) }, { argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 6783045015543232910422179840, coefficient := (-6783045015543232910422179840) }, { argument := 107955445921747473062376243200, coefficient := (-107955445921747473062376243200) }, { argument := 187383765878855357976815861760, coefficient := (-187383765878855357976815861760) }, { argument := 89063242885441665276460400640, coefficient := (-89063242885441665276460400640) }, { argument := 4403445820492331138070609920, coefficient := (-4403445820492331138070609920) }, { argument := 88921196246070944917167800320, coefficient := (-88921196246070944917167800320) }, { argument := 90483709279148868869386403840, coefficient := (-90483709279148868869386403840) }, { argument := 6795745655831035221083422720, coefficient := (-6795745655831035221083422720) }, { argument := 107955445921747473062376243200, coefficient := (-107955445921747473062376243200) }, { argument := 4403445820492331138070609920, coefficient := (-4403445820492331138070609920) }, { argument := 313535732120867060498042978304, coefficient := (-313535732120867060498042978304) }, { argument := 9461196200655895819296891207680, coefficient := (-9461196200655895819296891207680) }, { argument := 210053650647010529353029124096, coefficient := (-210053650647010529353029124096) }, { argument := 272502033271797443485010755584, coefficient := (-272502033271797443485010755584) }, { argument := 3650391820703453253351289913344, coefficient := (-3650391820703453253351289913344) }, { argument := 6602497181147925557772239765504, coefficient := (-6602497181147925557772239765504) }, { argument := 9461196202385278076207161671680, coefficient := (-9461196202385278076207161671680) }, { argument := 3650391820703453253351289913344, coefficient := (-3650391820703453253351289913344) }, { argument := 215730776340172976092300181504, coefficient := (-215730776340172976092300181504) }, { argument := 215730776340172976092300181504, coefficient := (-215730776340172976092300181504) }, { argument := 210053650647010529353029124096, coefficient := (-210053650647010529353029124096) }, { argument := 210053650647010529353029124096, coefficient := (-210053650647010529353029124096) }, { argument := 6602497181147925557772239765504, coefficient := (-6602497181147925557772239765504) }, { argument := 210053650647010529353029124096, coefficient := (-210053650647010529353029124096) }, { argument := 313535730391484803587772514304, coefficient := (-313535730391484803587772514304) }, { argument := 272502033271797443485010755584, coefficient := (-272502033271797443485010755584) }, { argument := 180933427001085400593358389248, coefficient := (-180933427001085400593358389248) }, { argument := 14136696334634861460430526611456, coefficient := (-14136696334634861460430526611456) }, { argument := 2666450306784135969242246807552, coefficient := (-2666450306784135969242246807552) }, { argument := 130123435545093039978778365788160, coefficient := (-130123435545093039978778365788160) }, { argument := 1662202788644656188618543464448, coefficient := (-1662202788644656188618543464448) }, { argument := 86573061908575843157215805440, coefficient := (-86573061908575843157215805440) }, { argument := 2649135694402420800610803646464, coefficient := (-2649135694402420800610803646464) }, { argument := 2770337981074426981030905774080, coefficient := (-2770337981074426981030905774080) }, { argument := 1662202788644656188618543464448, coefficient := (-1662202788644656188618543464448) }, { argument := 42438114947583878315667187826688, coefficient := (-42438114947583878315667187826688) }, { argument := 2718394143929281475136576290816, coefficient := (-2718394143929281475136576290816) }, { argument := 14136696359238206368740641079296, coefficient := (-14136696359238206368740641079296) }, { argument := 2649135694402420800610803646464, coefficient := (-2649135694402420800610803646464) }, { argument := 86573061908575843157215805440, coefficient := (-86573061908575843157215805440) }, { argument := 2718394143929281475136576290816, coefficient := (-2718394143929281475136576290816) }, { argument := 86573061908575843157215805440, coefficient := (-86573061908575843157215805440) }, { argument := 2649135694402420800610803646464, coefficient := (-2649135694402420800610803646464) }, { argument := 2770337981074426981030905774080, coefficient := (-2770337981074426981030905774080) }, { argument := 180933427001085400593358389248, coefficient := (-180933427001085400593358389248) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 486555748906740823716003840, coefficient := (-486555748906740823716003840) }, { argument := 156729999175750489511276052480, coefficient := (-156729999175750489511276052480) }, { argument := 1666889450642714429751866425344, coefficient := (-1666889450642714429751866425344) }, { argument := 156730471559972729065473835008, coefficient := (-156730471559972729065473835008) }, { argument := 486555748906740823716003840, coefficient := (-486555748906740823716003840) }, { argument := 252437594582674239061567209472, coefficient := (-252437594582674239061567209472) }, { argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }, { argument := 9483312605230440257883104870400, coefficient := (-9483312605230440257883104870400) }, { argument := 197524492995667032131281879040, coefficient := (-197524492995667032131281879040) }, { argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }, { argument := 9483310414192241359696554885120, coefficient := (-9483310414192241359696554885120) }, { argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }] }

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
def constantNumerator : ℤ := (-4083904416407458758703352752635904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3795178205, 157337245013, 975902967, 42831296885, 157337245013, 448419378618041,
    3795178205, 975902967, 3795178205, 2747525, 1770072975, 18825470455,
    885039155, 2747525, 1177371783, 184310949333, 46077754233, 4709554731,
    752927070997, 5428414961741, 1506138550665, 41612375, 7298419625, 1824605125,
    10402875, 1725130175, 302571625025, 75642915325, 431273475, 84074265,
    54164233035, 576059395923, 27082198143, 84074265, 10700325, 1876736475,
    469184175, 2675025, 2747525, 1770072975, 18825470455, 885039155,
    2747525, 95462577, 14944131027, 3736034127, 381855789, 469625375,
    82367878625, 20591972125, 117403875, 1648515, 1062043785, 11295282273,
    531023493, 1648515, 1725130175, 302571625025, 75642915325, 431273475,
    1346836755, 867689772345, 9228245617041, 433846193781
  ]
def negativeCoefficients : Array ℕ := #[
    17502170265438850948341432320, 725589973004336363601240522752, 18002232273022818118294044672, 197524492995667032131281879040, 725589973004336363601240522752, 252437668306239851146397089792,
    17502170265438850948341432320, 18002232273022818118294044672, 17502170265438850948341432320, 25341445255559417901875200, 8163020790403671328712294400, 86817158887641376549576376320,
    8163045393748579638826762240, 25341445255559417901875200, 5429668990152024552565112832, 212496057020518699078420267008, 212496134956859488996668997632, 5429746926492814470813843456,
    6781764152758496372430209024, 24447407598909192900272193536, 6783045015543232910422179840, 95951603990528687865856000, 16829009870614279758020608000, 16829011888226912820002816000,
    95949586377895625883648000, 3977879354007346459810201600, 697682666350323426539654348800, 697682749994778585766402457600, 3977795709552187233062092800, 775448224820118187797381120,
    249788436186352342658596208640, 2656605061961826122417037115392, 249789189048706536948098924544, 775448224820118187797381120, 98693078390258078947737600, 17309838724060402036821196800,
    17309840799319110329145753600, 98691003131549786623180800, 810926248177901372860006400, 261216665292917482518793420800, 2778149084404524049586444042240, 261217452599954548442456391680,
    810926248177901372860006400, 7043894906143166987111497728, 275670560459051285290923589632, 275670661565655553292975996928, 7043996012747434989163905024, 1082882387893109477343232000,
    189927397111218300126232576000, 189927419881418016111460352000, 1082859617693393492115456000, 486555748906740823716003840, 156729999175750489511276052480, 1666889450642714429751866425344,
    156730471559972729065473835008, 486555748906740823716003840, 3977879354007346459810201600, 697682666350323426539654348800, 697682749994778585766402457600, 3977795709552187233062092800,
    12422376464275226655499223040, 4001512791455879685334766714880, 42557771286721802784602339672064, 4001524852015553738952878850048
  ]
def negativeScales : Array ℕ := #[
    31, 37, 29, 35, 37, 48,
    31, 29, 31, 21, 30, 34,
    29, 21, 30, 37, 35, 32,
    39, 42, 40, 25, 32, 30,
    23, 30, 38, 36, 28, 26,
    35, 39, 34, 26, 23, 30,
    28, 21, 21, 30, 34, 29,
    21, 26, 33, 31, 28, 28,
    36, 34, 26, 20, 29, 33,
    28, 20, 30, 38, 36, 28,
    30, 39, 43, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31821520484873869, 37195069271000066, 29862162470556470, 35317946309997787, 37195069271000066, 48671841954578316,
    31821520484873869, 29862162470556470, 31821520484873869, 21389701177782373, 30721161693791430, 34131966867668019,
    29721166042067786, 21389701177782373, 30132922811402374, 37423350823244004, 35423351352375477, 32132943519398684,
    39453719175050855, 42303668146870785, 40453991629218129, 25310509295851609, 32764936955822540, 30764937128785751,
    23310478959408832, 30684058083022908, 38138485742633699, 36138485915596909, 28684027746580095, 26325160925587658,
    35656621441503757, 39067426615473308, 34656625789780103, 26325160925587658, 23351151280348956, 30805578940732813,
    28805579113696026, 21351120943906178, 21389701177782373, 30721161693791430, 34131966867668019, 29721166042067786,
    21389701177782373, 26508431946494939, 33798859958967373, 31798860488098854, 28508452654491249, 28806935122714766,
    36261362781631420, 34261362954594630, 26806904786271533, 20652735583639001, 29984196117868241, 33395001273501818,
    28984200466145881, 20652735583639001, 30684058083022908, 38138485742633699, 36138485915596909, 28684027746580095,
    30326927851761846, 39658388367679089, 43069193541647496, 38658392715955436
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
noncomputable def negativeCeiling : ℝ := 8060757171 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }, { argument := 725589973004336363601240522752, coefficient := (-725589973004336363601240522752) }, { argument := 18002232273022818118294044672, coefficient := (-18002232273022818118294044672) }, { argument := 197524492995667032131281879040, coefficient := (-197524492995667032131281879040) }, { argument := 725589973004336363601240522752, coefficient := (-725589973004336363601240522752) }, { argument := 252437668306239851146397089792, coefficient := (-252437668306239851146397089792) }, { argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }, { argument := 18002232273022818118294044672, coefficient := (-18002232273022818118294044672) }, { argument := 17502170265438850948341432320, coefficient := (-17502170265438850948341432320) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 8163020790403671328712294400, coefficient := (-8163020790403671328712294400) }, { argument := 86817158887641376549576376320, coefficient := (-86817158887641376549576376320) }, { argument := 8163045393748579638826762240, coefficient := (-8163045393748579638826762240) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 5429668990152024552565112832, coefficient := (-5429668990152024552565112832) }, { argument := 212496057020518699078420267008, coefficient := (-212496057020518699078420267008) }, { argument := 212496134956859488996668997632, coefficient := (-212496134956859488996668997632) }, { argument := 5429746926492814470813843456, coefficient := (-5429746926492814470813843456) }, { argument := 6781764152758496372430209024, coefficient := (-6781764152758496372430209024) }, { argument := 24447407598909192900272193536, coefficient := (-24447407598909192900272193536) }, { argument := 6783045015543232910422179840, coefficient := (-6783045015543232910422179840) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 3977879354007346459810201600, coefficient := (-3977879354007346459810201600) }, { argument := 697682666350323426539654348800, coefficient := (-697682666350323426539654348800) }, { argument := 697682749994778585766402457600, coefficient := (-697682749994778585766402457600) }, { argument := 3977795709552187233062092800, coefficient := (-3977795709552187233062092800) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }, { argument := 249788436186352342658596208640, coefficient := (-249788436186352342658596208640) }, { argument := 2656605061961826122417037115392, coefficient := (-2656605061961826122417037115392) }, { argument := 249789189048706536948098924544, coefficient := (-249789189048706536948098924544) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }, { argument := 98693078390258078947737600, coefficient := (-98693078390258078947737600) }, { argument := 17309838724060402036821196800, coefficient := (-17309838724060402036821196800) }, { argument := 17309840799319110329145753600, coefficient := (-17309840799319110329145753600) }, { argument := 98691003131549786623180800, coefficient := (-98691003131549786623180800) }, { argument := 810926248177901372860006400, coefficient := (-810926248177901372860006400) }, { argument := 261216665292917482518793420800, coefficient := (-261216665292917482518793420800) }, { argument := 2778149084404524049586444042240, coefficient := (-2778149084404524049586444042240) }, { argument := 261217452599954548442456391680, coefficient := (-261217452599954548442456391680) }, { argument := 810926248177901372860006400, coefficient := (-810926248177901372860006400) }, { argument := 7043894906143166987111497728, coefficient := (-7043894906143166987111497728) }, { argument := 275670560459051285290923589632, coefficient := (-275670560459051285290923589632) }, { argument := 275670661565655553292975996928, coefficient := (-275670661565655553292975996928) }, { argument := 7043996012747434989163905024, coefficient := (-7043996012747434989163905024) }, { argument := 1082882387893109477343232000, coefficient := (-1082882387893109477343232000) }, { argument := 189927397111218300126232576000, coefficient := (-189927397111218300126232576000) }, { argument := 189927419881418016111460352000, coefficient := (-189927419881418016111460352000) }, { argument := 1082859617693393492115456000, coefficient := (-1082859617693393492115456000) }, { argument := 486555748906740823716003840, coefficient := (-486555748906740823716003840) }, { argument := 156729999175750489511276052480, coefficient := (-156729999175750489511276052480) }, { argument := 1666889450642714429751866425344, coefficient := (-1666889450642714429751866425344) }, { argument := 156730471559972729065473835008, coefficient := (-156730471559972729065473835008) }, { argument := 486555748906740823716003840, coefficient := (-486555748906740823716003840) }, { argument := 3977879354007346459810201600, coefficient := (-3977879354007346459810201600) }, { argument := 697682666350323426539654348800, coefficient := (-697682666350323426539654348800) }, { argument := 697682749994778585766402457600, coefficient := (-697682749994778585766402457600) }, { argument := 3977795709552187233062092800, coefficient := (-3977795709552187233062092800) }, { argument := 12422376464275226655499223040, coefficient := (-12422376464275226655499223040) }, { argument := 4001512791455879685334766714880, coefficient := (-4001512791455879685334766714880) }, { argument := 42557771286721802784602339672064, coefficient := (-42557771286721802784602339672064) }, { argument := 4001524852015553738952878850048, coefficient := (-4001524852015553738952878850048) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
