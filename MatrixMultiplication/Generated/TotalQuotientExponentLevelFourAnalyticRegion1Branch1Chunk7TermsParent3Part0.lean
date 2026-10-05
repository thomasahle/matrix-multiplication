import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1734562638194503462628817455022080)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    257, 1025, 509, 1025, 6443246382819, 10359929645,
    197516573177973, 68375535657, 3380608621, 34133241883, 69466054567, 807394945813,
    10359929645, 3380608621, 108530205144571, 4657092751464965, 32648207345, 2647149207,
    567372254999, 1026205577215, 4657092528265619, 567372254999, 16765146215, 16765219943,
    32648207345, 32648059889, 1026205577215, 32648059889, 108530126354029, 2647149207,
    4509, 13527, 28557, 73647, 61623, 1723941,
    52605, 61623, 55611, 28557, 28557, 55611,
    1723941, 55611, 4509, 73647, 804791282025, 724214068344153,
    2309455995, 7086294970845717, 89978805, 149964675, 4588919055, 149964675,
    89978805, 73512683685, 4708890795, 362107392619777, 4588919055, 149964675,
    4708890795, 149964675, 4588919055, 149964675
  ]
def negativeCoefficients : Array ℕ := #[
    19884411881021420665567182848, 19826383441679918465181286400, 19690983749883079997614194688, 19826383441679918465181286400, 14508901004359972310180954112, 191106970782951648906256056320,
    444767782681908253856108642304, 157663250895935110347661246464, 7795152755620396205386760192, 157411794355431226599100383232, 160177816300973947833269878784, 14544734308416994438379732992,
    191106970782951648906256056320, 7795152755620396205386760192, 122194147861883360890064994304, 5243420295031863578403704668160, 75281640669827425558268477440, 97662567892904378217239937024,
    1308271347811253471416888066048, 2366268956237311365294514503680, 5243420043731740709669102944256, 1308271347811253471416888066048, 77315590396606342571082383360, 77315930406993109185537769472,
    75281640669827425558268477440, 75281300659440658943813091328, 2366268956237311365294514503680, 75281300659440658943813091328, 122194059151619463010211332096, 97662567892904378217239937024,
    340690407540147684296884224, 255517805655110763222663168, 269713239302616916735033344, 347788124363900761053069312, 4656102236382018352057417728, 8141081196844779039344295936,
    248420088831357686466478080, 4656102236382018352057417728, 262615522478863839978848256, 269713239302616916735033344, 269713239302616916735033344, 262615522478863839978848256,
    8141081196844779039344295936, 262615522478863839978848256, 340690407540147684296884224, 347788124363900761053069312, 7248915435677627511000268800, 815392552082799593474041577472,
    85203887378518491736666275840, 7978458847534547724316503441408, 53114111612582955887791964160, 2766359979822028952489164800, 84650615382554085946168442880, 88523519354304926479653273600,
    53114111612582955887791964160, 1356069662108758592510188584960, 86863703366411709108159774720, 815393359235264795279617949696, 84650615382554085946168442880, 2766359979822028952489164800,
    86863703366411709108159774720, 2766359979822028952489164800, 84650615382554085946168442880, 88523519354304926479653273600
  ]
def negativeScales : Array ℕ := #[
    8, 10, 8, 10, 42, 33,
    47, 35, 31, 34, 36, 39,
    33, 31, 46, 52, 34, 31,
    39, 39, 52, 39, 33, 33,
    34, 34, 39, 34, 46, 31,
    12, 13, 14, 16, 15, 20,
    15, 15, 15, 14, 14, 15,
    20, 15, 12, 16, 39, 49,
    31, 52, 26, 27, 32, 27,
    26, 36, 32, 48, 32, 27,
    32, 27, 32, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    8005624549193879, 10001408194392809, 8991521866745102, 10001408194392809, 42550924901572172, 33270295154489380,
    47488967040135917, 35992761200046075, 31654635856569269, 34990458413409423, 36015589108414732, 39554483599526506,
    33270295154489380, 31654635856569269, 46625089944816125, 52048351038718842, 34926284733946099, 31301792368854429,
    39045504647045045, 39900456914464217, 52048350969575148, 39045504647045045, 33964746027676632, 33964752372196882,
    34926284733946099, 34926278217982029, 39900456914464217, 34926278217982029, 46625088897450875, 31301792368854429,
    12138591794637521, 13723554295483443, 14801556808026795, 16168339138031573, 15911181303864252, 20717278970040312,
    15682912310909503, 15911181303864252, 15763082659843835, 14801556808026795, 14801556808026795, 15763082659843835,
    20717278970040312, 15763082659843835, 12138591794637521, 16168339138031573, 39549823720864718, 49363409530828448,
    31104905910933069, 52653952942998409, 26423081870959341, 27160047465125530, 32095507212930820, 27160047465125530,
    26423081870959341, 36097274139105008, 32132740119129795, 48363410958943384, 32095507212930820, 27160047465125530,
    32132740119129795, 27160047465125530, 32095507212930820, 27160047465125530
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
noncomputable def negativeCeiling : ℝ := 3604101117 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19884411881021420665567182848, coefficient := (-19884411881021420665567182848) }, { argument := 19826383441679918465181286400, coefficient := (-19826383441679918465181286400) }, { argument := 19690983749883079997614194688, coefficient := (-19690983749883079997614194688) }, { argument := 19826383441679918465181286400, coefficient := (-19826383441679918465181286400) }, { argument := 14508901004359972310180954112, coefficient := (-14508901004359972310180954112) }, { argument := 191106970782951648906256056320, coefficient := (-191106970782951648906256056320) }, { argument := 444767782681908253856108642304, coefficient := (-444767782681908253856108642304) }, { argument := 157663250895935110347661246464, coefficient := (-157663250895935110347661246464) }, { argument := 7795152755620396205386760192, coefficient := (-7795152755620396205386760192) }, { argument := 157411794355431226599100383232, coefficient := (-157411794355431226599100383232) }, { argument := 160177816300973947833269878784, coefficient := (-160177816300973947833269878784) }, { argument := 14544734308416994438379732992, coefficient := (-14544734308416994438379732992) }, { argument := 191106970782951648906256056320, coefficient := (-191106970782951648906256056320) }, { argument := 7795152755620396205386760192, coefficient := (-7795152755620396205386760192) }, { argument := 122194147861883360890064994304, coefficient := (-122194147861883360890064994304) }, { argument := 5243420295031863578403704668160, coefficient := (-5243420295031863578403704668160) }, { argument := 75281640669827425558268477440, coefficient := (-75281640669827425558268477440) }, { argument := 97662567892904378217239937024, coefficient := (-97662567892904378217239937024) }, { argument := 1308271347811253471416888066048, coefficient := (-1308271347811253471416888066048) }, { argument := 2366268956237311365294514503680, coefficient := (-2366268956237311365294514503680) }, { argument := 5243420043731740709669102944256, coefficient := (-5243420043731740709669102944256) }, { argument := 1308271347811253471416888066048, coefficient := (-1308271347811253471416888066048) }, { argument := 77315590396606342571082383360, coefficient := (-77315590396606342571082383360) }, { argument := 77315930406993109185537769472, coefficient := (-77315930406993109185537769472) }, { argument := 75281640669827425558268477440, coefficient := (-75281640669827425558268477440) }, { argument := 75281300659440658943813091328, coefficient := (-75281300659440658943813091328) }, { argument := 2366268956237311365294514503680, coefficient := (-2366268956237311365294514503680) }, { argument := 75281300659440658943813091328, coefficient := (-75281300659440658943813091328) }, { argument := 122194059151619463010211332096, coefficient := (-122194059151619463010211332096) }, { argument := 97662567892904378217239937024, coefficient := (-97662567892904378217239937024) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 248420088831357686466478080, coefficient := (-248420088831357686466478080) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 7248915435677627511000268800, coefficient := (-7248915435677627511000268800) }, { argument := 815392552082799593474041577472, coefficient := (-815392552082799593474041577472) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 7978458847534547724316503441408, coefficient := (-7978458847534547724316503441408) }, { argument := 53114111612582955887791964160, coefficient := (-53114111612582955887791964160) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 88523519354304926479653273600, coefficient := (-88523519354304926479653273600) }, { argument := 53114111612582955887791964160, coefficient := (-53114111612582955887791964160) }, { argument := 1356069662108758592510188584960, coefficient := (-1356069662108758592510188584960) }, { argument := 86863703366411709108159774720, coefficient := (-86863703366411709108159774720) }, { argument := 815393359235264795279617949696, coefficient := (-815393359235264795279617949696) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 86863703366411709108159774720, coefficient := (-86863703366411709108159774720) }, { argument := 2766359979822028952489164800, coefficient := (-2766359979822028952489164800) }, { argument := 84650615382554085946168442880, coefficient := (-84650615382554085946168442880) }, { argument := 88523519354304926479653273600, coefficient := (-88523519354304926479653273600) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3888914957463800160021015729012736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    804791282025, 117, 351, 741, 1911, 1599,
    44733, 1365, 1599, 1443, 741, 741,
    1443, 44733, 1443, 117, 1911, 8554245,
    4044227355, 153515645745, 16176920515, 8554245, 100437847917, 8662185,
    494759473448989, 97758945, 8662185, 123689883786235, 8662185, 8662185,
    359109441, 2227419, 97758945, 359109441, 12856120430967, 8662185,
    2227419, 8662185, 6443249340701, 10359932115, 197516684527499, 68375551959,
    3380609427, 34133250021, 69466071129, 807395316971, 10359932115, 3380609427,
    200288622328601, 8369832849153255, 121384980703, 9841963929, 2109459624601, 3815268126257,
    16739659203132029, 2109459624601, 62329471561, 62331127369, 121384980703, 121381669087,
    3815268126257, 121381669087, 400576957642115, 9841963929
  ]
def negativeCoefficients : Array ℕ := #[
    7248915435677627511000268800, 17680540111863951680077824, 13260405083897963760058368, 13997094255225628413394944, 18048884697527784006746112, 241634048195474006294396928,
    422491239756415678688526336, 12892060498234131433390080, 241634048195474006294396928, 13628749669561796086726656, 13997094255225628413394944, 13997094255225628413394944,
    13628749669561796086726656, 422491239756415678688526336, 13628749669561796086726656, 17680540111863951680077824, 18048884697527784006746112, 157797968258809563363409920,
    18650706748395076242552913920, 176991489273017105869040517120, 18650719540059169855520112640, 157797968258809563363409920, 7237309671246331965773709312, 159789109814125772364840960,
    278524822532861208725257453568, 1803334239330848002403205120, 159789109814125772364840960, 278524857264593950458804961280, 159789109814125772364840960, 159789109814125772364840960,
    6624399952579899877182406656, 164354512951672223003836416, 1803334239330848002403205120, 6624399952579899877182406656, 7237352397791650205562568704, 159789109814125772364840960,
    164354512951672223003836416, 159789109814125772364840960, 14508907664918108813129678848, 191107016346409510968848547840, 444768033418750154596786634752, 157663288485787846549300051968,
    7795154614129861631624085504, 157411831885332044561183145984, 160177854490345866430469111808, 14544740994605116420693950464, 191107016346409510968848547840, 7795154614129861631624085504,
    451009882442818734225042178048, 18847188050299968037557884682240, 279894709177551691566867808256, 363104379561887848454871318528, 4864082728604759028174424113152, 8797409337205532511152493297664,
    18847180737383624953069196804096, 4864082728604759028174424113152, 287443952533831196305883398144, 287451588600433996522193944576, 279894709177551691566867808256, 279887073110948891350557261824,
    8797409337205532511152493297664, 279887073110948891350557261824, 451009559292559018497419509760, 363104379561887848454871318528
  ]
def negativeScales : Array ℕ := #[
    39, 6, 8, 9, 10, 10,
    15, 10, 10, 10, 9, 9,
    10, 15, 10, 6, 10, 23,
    31, 37, 33, 23, 36, 23,
    48, 26, 23, 46, 23, 23,
    28, 21, 26, 28, 43, 23,
    21, 23, 42, 33, 47, 35,
    31, 34, 36, 39, 33, 31,
    47, 52, 36, 33, 40, 41,
    53, 40, 35, 35, 36, 36,
    41, 36, 48, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39549823720864718, 6870364722125690, 8455327220304618, 9533329732306630, 10900112067353854, 10642954223498123,
    15449051894878119, 10414685235807227, 10642954223498123, 10494855584491427, 9533329732306630, 9533329732306630,
    10494855584491427, 15449051894878119, 10494855584491427, 6870364722125690, 10900112067353854, 23028209096999409,
    31913216963258337, 37159594740975035, 33913217952736435, 23028209096999409, 36547512065171100, 23046299553982304,
    48813720660938378, 26542725380102868, 23046299553982304, 46813720840840822, 23046299553982304, 23046299553982304,
    28419848341104097, 21086941538479650, 26542725380102868, 28419848341104097, 43547520582312952, 23046299553982304,
    21086941538479650, 23046299553982304, 42550925563865752, 33270295498454681, 47488967853451788, 35992761544011494,
    31654636200534571, 34990458757374838, 36015589452380034, 39554484262730662, 33270295498454681, 31654636200534571,
    47509073797620391, 52894120238772002, 36820798968759576, 33196299082957039, 40940010621850309, 41794921588381795,
    53894119678990303, 40940010621850309, 35859195432342606, 35859233757621065, 36820798968759576, 36820759608723278,
    41794921588381795, 36820759608723278, 48509072763923654, 33196299082957039
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
noncomputable def negativeCeiling : ℝ := 40491036997 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7248915435677627511000268800, coefficient := (-7248915435677627511000268800) }, { argument := 17680540111863951680077824, coefficient := (-17680540111863951680077824) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 18048884697527784006746112, coefficient := (-18048884697527784006746112) }, { argument := 241634048195474006294396928, coefficient := (-241634048195474006294396928) }, { argument := 422491239756415678688526336, coefficient := (-422491239756415678688526336) }, { argument := 12892060498234131433390080, coefficient := (-12892060498234131433390080) }, { argument := 241634048195474006294396928, coefficient := (-241634048195474006294396928) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 422491239756415678688526336, coefficient := (-422491239756415678688526336) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 17680540111863951680077824, coefficient := (-17680540111863951680077824) }, { argument := 18048884697527784006746112, coefficient := (-18048884697527784006746112) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }, { argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 7237309671246331965773709312, coefficient := (-7237309671246331965773709312) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 278524822532861208725257453568, coefficient := (-278524822532861208725257453568) }, { argument := 1803334239330848002403205120, coefficient := (-1803334239330848002403205120) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 278524857264593950458804961280, coefficient := (-278524857264593950458804961280) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 6624399952579899877182406656, coefficient := (-6624399952579899877182406656) }, { argument := 164354512951672223003836416, coefficient := (-164354512951672223003836416) }, { argument := 1803334239330848002403205120, coefficient := (-1803334239330848002403205120) }, { argument := 6624399952579899877182406656, coefficient := (-6624399952579899877182406656) }, { argument := 7237352397791650205562568704, coefficient := (-7237352397791650205562568704) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 164354512951672223003836416, coefficient := (-164354512951672223003836416) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 14508907664918108813129678848, coefficient := (-14508907664918108813129678848) }, { argument := 191107016346409510968848547840, coefficient := (-191107016346409510968848547840) }, { argument := 444768033418750154596786634752, coefficient := (-444768033418750154596786634752) }, { argument := 157663288485787846549300051968, coefficient := (-157663288485787846549300051968) }, { argument := 7795154614129861631624085504, coefficient := (-7795154614129861631624085504) }, { argument := 157411831885332044561183145984, coefficient := (-157411831885332044561183145984) }, { argument := 160177854490345866430469111808, coefficient := (-160177854490345866430469111808) }, { argument := 14544740994605116420693950464, coefficient := (-14544740994605116420693950464) }, { argument := 191107016346409510968848547840, coefficient := (-191107016346409510968848547840) }, { argument := 7795154614129861631624085504, coefficient := (-7795154614129861631624085504) }, { argument := 451009882442818734225042178048, coefficient := (-451009882442818734225042178048) }, { argument := 18847188050299968037557884682240, coefficient := (-18847188050299968037557884682240) }, { argument := 279894709177551691566867808256, coefficient := (-279894709177551691566867808256) }, { argument := 363104379561887848454871318528, coefficient := (-363104379561887848454871318528) }, { argument := 4864082728604759028174424113152, coefficient := (-4864082728604759028174424113152) }, { argument := 8797409337205532511152493297664, coefficient := (-8797409337205532511152493297664) }, { argument := 18847180737383624953069196804096, coefficient := (-18847180737383624953069196804096) }, { argument := 4864082728604759028174424113152, coefficient := (-4864082728604759028174424113152) }, { argument := 287443952533831196305883398144, coefficient := (-287443952533831196305883398144) }, { argument := 287451588600433996522193944576, coefficient := (-287451588600433996522193944576) }, { argument := 279894709177551691566867808256, coefficient := (-279894709177551691566867808256) }, { argument := 279887073110948891350557261824, coefficient := (-279887073110948891350557261824) }, { argument := 8797409337205532511152493297664, coefficient := (-8797409337205532511152493297664) }, { argument := 279887073110948891350557261824, coefficient := (-279887073110948891350557261824) }, { argument := 451009559292559018497419509760, coefficient := (-451009559292559018497419509760) }, { argument := 363104379561887848454871318528, coefficient := (-363104379561887848454871318528) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
