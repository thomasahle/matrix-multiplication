import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

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
def constantNumerator : ℤ := (-2955048158823468505409682422104064)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1047, 1001, 1047, 1001, 58407688415331, 22799,
    306095524075421, 22393, 981, 22367, 20569, 58437753186403,
    22799, 487, 836928468520315, 52775010692035205, 5779728425, 6577985143,
    100521026051, 165651236273, 26387506611724101, 100521026051, 5779728425, 5653659539,
    1387094421, 5653659539, 165651236273, 1387094421, 418462968553659, 6577985143,
    4941751170837, 162179167593537, 14719058543, 6635195599056421, 507119479, 1124118891,
    14719058543, 14416282223, 507119479, 184225106519, 7151767545, 324358372965333,
    14719058543, 1124118891, 7151767545, 1124118891, 14723646063, 14416282223,
    627560001411, 1995, 3325, 101745, 3325, 104405,
    3325, 101745, 57855, 104405, 1629915, 1995,
    3325, 101745, 3325, 1995
  ]
def negativeCoefficients : Array ℕ := #[
    40503850660368535869355720704, 38724311853895801724188229632, 40503850660368535869355720704, 38724311853895801724188229632, 131522421891428363804331737088, 220498398091151444433008852992,
    1378531688165842702755814178816, 216571807029043128873563193344, 9487649832335609763094069248, 216320350458563286005224308736, 198931161469226459956250673152, 131590121737326783038115282944,
    220498398091151444433008852992, 9419949986437190529310523392, 235574421185240657862212976640, 14854844905445230716889050644480, 53308585535759695334499942400, 60671204226792363713619820544,
    927142820794743851099732574208, 1527862980510811731159452483584, 14854845617974645092515957440512, 927142820794743851099732574208, 53308585535759695334499942400, 52145805297909862804605632512,
    51174751580514663641930268672, 52145805297909862804605632512, 1527862980510811731159452483584, 51174751580514663641930268672, 235573708655826282235306180608, 60671204226792363713619820544,
    11127834365769612759794712576, 1460780077483020907374868168704, 33939838243583649676773031936, 14941132213720426298111487377408, 18709406487811850825659056128, 1296020843168700213667823616,
    33939838243583649676773031936, 33241683582756201328380215296, 18709406487811850825659056128, 424794173988484266740666073088, 32981706394319264750952775680, 1460780247621174062480955015168,
    33939838243583649676773031936, 1296020843168700213667823616, 32981706394319264750952775680, 1296020843168700213667823616, 33950416344505277682051710976, 33241683582756201328380215296,
    11305115954028830175919079424, 75368969066599537610588160, 2009839175109321002949017600, 1921908711198288209069998080, 62807474222166281342156800, 1972154690576021234143723520,
    62807474222166281342156800, 1921908711198288209069998080, 1092850051465693295353528320, 1972154690576021234143723520, 30788223863705911113925263360, 1205903505065592601769410560,
    2009839175109321002949017600, 1921908711198288209069998080, 62807474222166281342156800, 1205903505065592601769410560
  ]
def negativeScales : Array ℕ := #[
    10, 9, 10, 9, 45, 14,
    48, 14, 9, 14, 14, 45,
    14, 8, 49, 55, 32, 32,
    36, 37, 54, 36, 32, 32,
    30, 32, 37, 30, 48, 32,
    42, 47, 33, 52, 28, 30,
    33, 33, 28, 37, 32, 48,
    33, 30, 32, 30, 33, 33,
    39, 10, 11, 16, 11, 16,
    11, 16, 15, 16, 20, 10,
    11, 16, 11, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10032045726930809, 9967226272738856, 10032045726930809, 9967226272738856, 45731223522457095, 14476682926453630,
    48120975277432358, 14450760199173326, 9938109334735015, 14449084145764836, 14328184035827953, 45731965944183425,
    14476682926453630, 8927777969209522, 49572097650698261, 55550704484056658, 32428354559668908, 32614998603708924,
    36548706346228912, 37269358014208413, 54550704553257154, 36548706346228912, 32428354559668908, 32396537861282454,
    30369418850784049, 32396537861282454, 37269358014208413, 30369418850784049, 48572093287048752, 32614998603708924,
    42168159507947743, 47204581841321496, 33776966346295726, 52559060418768889, 28917750456006484, 30066147482414591,
    33776966346295726, 33746980108809429, 28917750456006484, 37422678731586609, 32735652699294658, 48204582009353261,
    33776966346295726, 30066147482414591, 32735652699294658, 30066147482414591, 33777415924046968, 33746980108809429,
    39190962446409666, 10962173043893966, 11699138625346849, 16634598373095531, 11699138625346849, 16671831279316955,
    11699138625346849, 16634598373095531, 15820154027206250, 16671831279316955, 20636365299270394, 10962173043893966,
    11699138625346849, 16634598373095531, 11699138625346849, 10962173043893966
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
noncomputable def negativeCeiling : ℝ := 34936266569 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 40503850660368535869355720704, coefficient := (-40503850660368535869355720704) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 40503850660368535869355720704, coefficient := (-40503850660368535869355720704) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 131522421891428363804331737088, coefficient := (-131522421891428363804331737088) }, { argument := 220498398091151444433008852992, coefficient := (-220498398091151444433008852992) }, { argument := 1378531688165842702755814178816, coefficient := (-1378531688165842702755814178816) }, { argument := 216571807029043128873563193344, coefficient := (-216571807029043128873563193344) }, { argument := 9487649832335609763094069248, coefficient := (-9487649832335609763094069248) }, { argument := 216320350458563286005224308736, coefficient := (-216320350458563286005224308736) }, { argument := 198931161469226459956250673152, coefficient := (-198931161469226459956250673152) }, { argument := 131590121737326783038115282944, coefficient := (-131590121737326783038115282944) }, { argument := 220498398091151444433008852992, coefficient := (-220498398091151444433008852992) }, { argument := 9419949986437190529310523392, coefficient := (-9419949986437190529310523392) }, { argument := 235574421185240657862212976640, coefficient := (-235574421185240657862212976640) }, { argument := 14854844905445230716889050644480, coefficient := (-14854844905445230716889050644480) }, { argument := 53308585535759695334499942400, coefficient := (-53308585535759695334499942400) }, { argument := 60671204226792363713619820544, coefficient := (-60671204226792363713619820544) }, { argument := 927142820794743851099732574208, coefficient := (-927142820794743851099732574208) }, { argument := 1527862980510811731159452483584, coefficient := (-1527862980510811731159452483584) }, { argument := 14854845617974645092515957440512, coefficient := (-14854845617974645092515957440512) }, { argument := 927142820794743851099732574208, coefficient := (-927142820794743851099732574208) }, { argument := 53308585535759695334499942400, coefficient := (-53308585535759695334499942400) }, { argument := 52145805297909862804605632512, coefficient := (-52145805297909862804605632512) }, { argument := 51174751580514663641930268672, coefficient := (-51174751580514663641930268672) }, { argument := 52145805297909862804605632512, coefficient := (-52145805297909862804605632512) }, { argument := 1527862980510811731159452483584, coefficient := (-1527862980510811731159452483584) }, { argument := 51174751580514663641930268672, coefficient := (-51174751580514663641930268672) }, { argument := 235573708655826282235306180608, coefficient := (-235573708655826282235306180608) }, { argument := 60671204226792363713619820544, coefficient := (-60671204226792363713619820544) }, { argument := 11127834365769612759794712576, coefficient := (-11127834365769612759794712576) }, { argument := 1460780077483020907374868168704, coefficient := (-1460780077483020907374868168704) }, { argument := 33939838243583649676773031936, coefficient := (-33939838243583649676773031936) }, { argument := 14941132213720426298111487377408, coefficient := (-14941132213720426298111487377408) }, { argument := 18709406487811850825659056128, coefficient := (-18709406487811850825659056128) }, { argument := 1296020843168700213667823616, coefficient := (-1296020843168700213667823616) }, { argument := 33939838243583649676773031936, coefficient := (-33939838243583649676773031936) }, { argument := 33241683582756201328380215296, coefficient := (-33241683582756201328380215296) }, { argument := 18709406487811850825659056128, coefficient := (-18709406487811850825659056128) }, { argument := 424794173988484266740666073088, coefficient := (-424794173988484266740666073088) }, { argument := 32981706394319264750952775680, coefficient := (-32981706394319264750952775680) }, { argument := 1460780247621174062480955015168, coefficient := (-1460780247621174062480955015168) }, { argument := 33939838243583649676773031936, coefficient := (-33939838243583649676773031936) }, { argument := 1296020843168700213667823616, coefficient := (-1296020843168700213667823616) }, { argument := 32981706394319264750952775680, coefficient := (-32981706394319264750952775680) }, { argument := 1296020843168700213667823616, coefficient := (-1296020843168700213667823616) }, { argument := 33950416344505277682051710976, coefficient := (-33950416344505277682051710976) }, { argument := 33241683582756201328380215296, coefficient := (-33241683582756201328380215296) }, { argument := 11305115954028830175919079424, coefficient := (-11305115954028830175919079424) }, { argument := 75368969066599537610588160, coefficient := (-75368969066599537610588160) }, { argument := 2009839175109321002949017600, coefficient := (-2009839175109321002949017600) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1972154690576021234143723520, coefficient := (-1972154690576021234143723520) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 1092850051465693295353528320, coefficient := (-1092850051465693295353528320) }, { argument := 1972154690576021234143723520, coefficient := (-1972154690576021234143723520) }, { argument := 30788223863705911113925263360, coefficient := (-30788223863705911113925263360) }, { argument := 1205903505065592601769410560, coefficient := (-1205903505065592601769410560) }, { argument := 2009839175109321002949017600, coefficient := (-2009839175109321002949017600) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1205903505065592601769410560, coefficient := (-1205903505065592601769410560) }] }

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
def constantNumerator : ℤ := (-42115826477126387979211715865739264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3325, 51205, 57855, 1995, 4938788221107, 3819,
    181349833937229, 60099, 1809, 362686220796403, 1809, 1809,
    154971, 1809, 60099, 154971, 9891030268429, 1809,
    1809, 3819, 58407662573469, 22799, 306095398922339, 22393,
    981, 22367, 20569, 58437727344541, 22799, 487,
    1465059828806277, 93161632576703867, 19730051235, 22420116459, 346474013607, 563074137963,
    46580818927542459, 346474013607, 19730051235, 19302711759, 9463036437, 19302711759,
    563074137963, 9463036437, 732527275212613, 22420116459, 181417730602731, 6002554729851327,
    245601009997, 246063925650429403, 8106649061, 18888707649, 245601009997, 245463814477,
    8106649061, 3032048466181, 121393552875, 12005110854803499, 245601009997, 18888707649,
    121393552875, 18888707649, 245603088717, 245463814477
  ]
def negativeCoefficients : Array ℕ := #[
    62807474222166281342156800, 1934470206042721465338429440, 1092850051465693295353528320, 75368969066599537610588160, 11121162396119640003928129536, 72138870392316700284420096,
    408363522271702926943995297792, 567619006507965615395831808, 68342087740089505532608512, 408348382207773496950466281472, 68342087740089505532608512, 68342087740089505532608512,
    2927319424867167153646731264, 68342087740089505532608512, 567619006507965615395831808, 2927319424867167153646731264, 11136310057801785356578717696, 68342087740089505532608512,
    68342087740089505532608512, 72138870392316700284420096, 131522363700728326924441485312, 220498398091151444433008852992, 1378531124526469243286683910144, 216571807029043128873563193344,
    9487649832335609763094069248, 216320350458563286005224308736, 198931161469226459956250673152, 131590063546626746158225031168, 220498398091151444433008852992, 9419949986437190529310523392,
    824755362385928969849011175424, 52445336719708824566724510613504, 181977602846611034946278522880, 206789075210968113685695823872, 3195658728599644898783926419456, 5193442258764042353909226799104,
    52445339691173191367110390972416, 3195658728599644898783926419456, 181977602846611034946278522880, 178036091873428462364390326272, 174562211313527300697140232192, 178036091873428462364390326272,
    5193442258764042353909226799104, 174562211313527300697140232192, 824752390921562169463130816512, 206789075210968113685695823872, 408516411970430180149363212288, 54066206489258889119692052496384,
    1132634743914810022828900876288, 554086701934297645969207086546944, 598165122094579405578309730304, 43554394485527878426687438848, 1132634743914810022828900876288, 1132002041253435147763169886208,
    598165122094579405578309730304, 13982855518681124396045512474624, 1119657901041726675744718848000, 54066212772234534805956150165504, 1132634743914810022828900876288, 43554394485527878426687438848,
    1119657901041726675744718848000, 43554394485527878426687438848, 1132644330318770248208684679168, 1132002041253435147763169886208
  ]
def negativeScales : Array ℕ := #[
    11, 15, 15, 10, 42, 11,
    47, 15, 10, 48, 10, 10,
    17, 10, 15, 17, 43, 10,
    10, 11, 45, 14, 48, 14,
    9, 14, 14, 45, 14, 8,
    50, 56, 34, 34, 38, 39,
    55, 38, 34, 34, 33, 34,
    39, 33, 49, 34, 47, 52,
    37, 57, 32, 34, 37, 37,
    32, 41, 36, 53, 37, 34,
    36, 34, 37, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11699138625346849, 15643997071101728, 15820154027206250, 10962173043893966, 42167294244860286, 11898979208910875,
    47365768752650232, 15875053368150273, 10820976693606152, 48365715263788290, 10820976693606152, 10820976693606152,
    17241638741093964, 10820976693606152, 15875053368150273, 17241638741093964, 43169257941305072, 10820976693606152,
    10820976693606152, 11898979208910875, 45731222884151839, 14476682926453630, 48120974687558434, 14450760199173326,
    9938109334735015, 14449084145764836, 14328184035827953, 45731965306206561, 14476682926453630, 8927777969209522,
    50379881004653984, 56370585439945774, 34199675651330658, 34384074720968145, 38333956194547102, 39034533933082179,
    55370585521686441, 38333956194547102, 34199675651330658, 34168084488928696, 33139656034348941, 34168084488928696,
    39034533933082179, 33139656034348941, 49379875806840397, 34384074720968145, 47366308790918982, 52414498075972742,
    37837525538708873, 57771810779570622, 32916458549604686, 34136804945879944, 37837525538708873, 37836719407636906,
    32916458549604686, 41463429953292040, 36820900847868060, 53414498243626770, 37837525538708873, 34136804945879944,
    36820900847868060, 34136804945879944, 37837537749352565, 37836719407636906
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
noncomputable def negativeCeiling : ℝ := 547596793389 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1934470206042721465338429440, coefficient := (-1934470206042721465338429440) }, { argument := 1092850051465693295353528320, coefficient := (-1092850051465693295353528320) }, { argument := 75368969066599537610588160, coefficient := (-75368969066599537610588160) }, { argument := 11121162396119640003928129536, coefficient := (-11121162396119640003928129536) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 408363522271702926943995297792, coefficient := (-408363522271702926943995297792) }, { argument := 567619006507965615395831808, coefficient := (-567619006507965615395831808) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 408348382207773496950466281472, coefficient := (-408348382207773496950466281472) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 2927319424867167153646731264, coefficient := (-2927319424867167153646731264) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 567619006507965615395831808, coefficient := (-567619006507965615395831808) }, { argument := 2927319424867167153646731264, coefficient := (-2927319424867167153646731264) }, { argument := 11136310057801785356578717696, coefficient := (-11136310057801785356578717696) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 131522363700728326924441485312, coefficient := (-131522363700728326924441485312) }, { argument := 220498398091151444433008852992, coefficient := (-220498398091151444433008852992) }, { argument := 1378531124526469243286683910144, coefficient := (-1378531124526469243286683910144) }, { argument := 216571807029043128873563193344, coefficient := (-216571807029043128873563193344) }, { argument := 9487649832335609763094069248, coefficient := (-9487649832335609763094069248) }, { argument := 216320350458563286005224308736, coefficient := (-216320350458563286005224308736) }, { argument := 198931161469226459956250673152, coefficient := (-198931161469226459956250673152) }, { argument := 131590063546626746158225031168, coefficient := (-131590063546626746158225031168) }, { argument := 220498398091151444433008852992, coefficient := (-220498398091151444433008852992) }, { argument := 9419949986437190529310523392, coefficient := (-9419949986437190529310523392) }, { argument := 824755362385928969849011175424, coefficient := (-824755362385928969849011175424) }, { argument := 52445336719708824566724510613504, coefficient := (-52445336719708824566724510613504) }, { argument := 181977602846611034946278522880, coefficient := (-181977602846611034946278522880) }, { argument := 206789075210968113685695823872, coefficient := (-206789075210968113685695823872) }, { argument := 3195658728599644898783926419456, coefficient := (-3195658728599644898783926419456) }, { argument := 5193442258764042353909226799104, coefficient := (-5193442258764042353909226799104) }, { argument := 52445339691173191367110390972416, coefficient := (-52445339691173191367110390972416) }, { argument := 3195658728599644898783926419456, coefficient := (-3195658728599644898783926419456) }, { argument := 181977602846611034946278522880, coefficient := (-181977602846611034946278522880) }, { argument := 178036091873428462364390326272, coefficient := (-178036091873428462364390326272) }, { argument := 174562211313527300697140232192, coefficient := (-174562211313527300697140232192) }, { argument := 178036091873428462364390326272, coefficient := (-178036091873428462364390326272) }, { argument := 5193442258764042353909226799104, coefficient := (-5193442258764042353909226799104) }, { argument := 174562211313527300697140232192, coefficient := (-174562211313527300697140232192) }, { argument := 824752390921562169463130816512, coefficient := (-824752390921562169463130816512) }, { argument := 206789075210968113685695823872, coefficient := (-206789075210968113685695823872) }, { argument := 408516411970430180149363212288, coefficient := (-408516411970430180149363212288) }, { argument := 54066206489258889119692052496384, coefficient := (-54066206489258889119692052496384) }, { argument := 1132634743914810022828900876288, coefficient := (-1132634743914810022828900876288) }, { argument := 554086701934297645969207086546944, coefficient := (-554086701934297645969207086546944) }, { argument := 598165122094579405578309730304, coefficient := (-598165122094579405578309730304) }, { argument := 43554394485527878426687438848, coefficient := (-43554394485527878426687438848) }, { argument := 1132634743914810022828900876288, coefficient := (-1132634743914810022828900876288) }, { argument := 1132002041253435147763169886208, coefficient := (-1132002041253435147763169886208) }, { argument := 598165122094579405578309730304, coefficient := (-598165122094579405578309730304) }, { argument := 13982855518681124396045512474624, coefficient := (-13982855518681124396045512474624) }, { argument := 1119657901041726675744718848000, coefficient := (-1119657901041726675744718848000) }, { argument := 54066212772234534805956150165504, coefficient := (-54066212772234534805956150165504) }, { argument := 1132634743914810022828900876288, coefficient := (-1132634743914810022828900876288) }, { argument := 43554394485527878426687438848, coefficient := (-43554394485527878426687438848) }, { argument := 1119657901041726675744718848000, coefficient := (-1119657901041726675744718848000) }, { argument := 43554394485527878426687438848, coefficient := (-43554394485527878426687438848) }, { argument := 1132644330318770248208684679168, coefficient := (-1132644330318770248208684679168) }, { argument := 1132002041253435147763169886208, coefficient := (-1132002041253435147763169886208) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
