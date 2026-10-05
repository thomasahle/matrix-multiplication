import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 14, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-64152517253897982802134535503872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6883405065, 1094279625, 9858375, 76895325, 76895325, 76895325,
    76895325, 76895325, 169764711, 92668725, 9834545, 238481355,
    78500695, 2200213365, 2587935, 6038515, 78500695, 78500695,
    2587935, 968750335, 38819025, 238481355, 78500695, 6038515,
    38819025, 6038515, 78500695, 78500695, 668535, 5870909,
    27277521, 1813968591, 429262041, 12920931, 1813968157, 12920931,
    12920931, 1106893089, 12920931, 429262041, 1106893089, 46967489,
    12920931, 12920931, 27277521, 720839, 115079923, 4593298297,
    115079923, 2883027, 35898331, 1325677605, 10605418243, 287189245,
    3008053, 10761111, 752013, 2999591, 110770905, 886167023,
    23996945, 3008053, 10761111, 752013
  ]
def negativeCoefficients : Array ℕ := #[
    7936025724358191308278333440, 1261618511715616281329664000, 90927460303828200456192000, 88654273796232495444787200, 88654273796232495444787200, 88654273796232495444787200,
    2836936761479439854233190400, 88654273796232495444787200, 195725386035266545501863936, 106839765856998135536025600, 181415334696379902297374720, 17596818088145894983304478720,
    2896164460546662059988746240, 162347091406841202374722191360, 1527647187980656910763294720, 111390940790256233076490240, 2896164460546662059988746240, 2896164460546662059988746240,
    1527647187980656910763294720, 35740579002130785641399582720, 2864338477463731707681177600, 17596818088145894983304478720, 2896164460546662059988746240, 111390940790256233076490240,
    2864338477463731707681177600, 111390940790256233076490240, 2896164460546662059988746240, 2896164460546662059988746240, 197316704789078641433640960, 433196623212152279873355776,
    251590724426118921053011968, 8365453588981128872029323264, 1979621752721304141969752064, 238349107351060030471274496, 8365451587509396874542972928, 238349107351060030471274496,
    238349107351060030471274496, 10209286764870404638519590912, 238349107351060030471274496, 1979621752721304141969752064, 10209286764870404638519590912, 433198624683884277359706112,
    238349107351060030471274496, 238349107351060030471274496, 251590724426118921053011968, 106377060410789755818606592, 16982799100825612194670444544, 169462796277929851820812795904,
    16982799100825612194670444544, 106364922453189254933643264, 5297658597042511054182023168, 195635484029465774815382077440, 195635436123271415391676530688, 5297706503236870477887569920,
    3551282166473871223498473472, 12704477476209962668800344064, 3551280985882250506087170048, 221330750011210030565556224, 8173450141392774958594129920, 8173448139921042961107779584,
    221332751482942028051906560, 3551282166473871223498473472, 12704477476209962668800344064, 3551280985882250506087170048
  ]
def negativeScales : Array ℕ := #[
    32, 30, 23, 26, 26, 26,
    26, 26, 27, 26, 23, 27,
    26, 31, 21, 22, 26, 26,
    21, 29, 25, 27, 26, 22,
    25, 22, 26, 26, 19, 22,
    24, 30, 28, 23, 30, 23,
    23, 30, 23, 28, 30, 25,
    23, 23, 24, 19, 26, 32,
    26, 21, 25, 30, 33, 28,
    21, 23, 19, 21, 26, 29,
    24, 21, 23, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32680475264183602, 30027334296004841, 23232918429654735, 26196392553629621, 26196392553629621, 26196392553629621,
    26196392553629621, 26196392553629621, 27338961356055840, 26465579186445092, 23229426876385346, 27829301237808821,
    26226202091064399, 31034996289418702, 21303369951586859, 22525762372923933, 26226202091064399, 26226202091064399,
    21303369951586859, 29851549665050376, 25210260547195377, 27829301237808821, 26226202091064399, 22525762372923933,
    25210260547195377, 22525762372923933, 26226202091064399, 26226202091064399, 19350643566549961, 22485152464186640,
    24701209201481082, 30756502329956927, 28677283362203151, 23623206689415947, 30756501984785721, 23623206689415947,
    23623206689415947, 30043868737878057, 23623206689415947, 28677283362203151, 30043868737878057, 25485159129766465,
    23623206689415947, 23623206689415947, 24701209201481082, 19459317542725530, 26778060920391783, 32096883331781654,
    26778060920391783, 21459152917285642, 25097413435446606, 30304082819316315, 33304082466036654, 28097426481533905,
    21520398555942497, 23359323696701575, 19520398076331506, 21516334369213142, 26723003753205601, 29723003399925939,
    24516347415300441, 21520398555942497, 23359323696701575, 19520398076331506
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
noncomputable def negativeCeiling : ℝ := 359917633 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7936025724358191308278333440, coefficient := (-7936025724358191308278333440) }, { argument := 1261618511715616281329664000, coefficient := (-1261618511715616281329664000) }, { argument := 90927460303828200456192000, coefficient := (-90927460303828200456192000) }, { argument := 88654273796232495444787200, coefficient := (-88654273796232495444787200) }, { argument := 88654273796232495444787200, coefficient := (-88654273796232495444787200) }, { argument := 88654273796232495444787200, coefficient := (-88654273796232495444787200) }, { argument := 2836936761479439854233190400, coefficient := (-2836936761479439854233190400) }, { argument := 88654273796232495444787200, coefficient := (-88654273796232495444787200) }, { argument := 195725386035266545501863936, coefficient := (-195725386035266545501863936) }, { argument := 106839765856998135536025600, coefficient := (-106839765856998135536025600) }, { argument := 181415334696379902297374720, coefficient := (-181415334696379902297374720) }, { argument := 17596818088145894983304478720, coefficient := (-17596818088145894983304478720) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 162347091406841202374722191360, coefficient := (-162347091406841202374722191360) }, { argument := 1527647187980656910763294720, coefficient := (-1527647187980656910763294720) }, { argument := 111390940790256233076490240, coefficient := (-111390940790256233076490240) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 1527647187980656910763294720, coefficient := (-1527647187980656910763294720) }, { argument := 35740579002130785641399582720, coefficient := (-35740579002130785641399582720) }, { argument := 2864338477463731707681177600, coefficient := (-2864338477463731707681177600) }, { argument := 17596818088145894983304478720, coefficient := (-17596818088145894983304478720) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 111390940790256233076490240, coefficient := (-111390940790256233076490240) }, { argument := 2864338477463731707681177600, coefficient := (-2864338477463731707681177600) }, { argument := 111390940790256233076490240, coefficient := (-111390940790256233076490240) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 2896164460546662059988746240, coefficient := (-2896164460546662059988746240) }, { argument := 197316704789078641433640960, coefficient := (-197316704789078641433640960) }, { argument := 433196623212152279873355776, coefficient := (-433196623212152279873355776) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 8365453588981128872029323264, coefficient := (-8365453588981128872029323264) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 8365451587509396874542972928, coefficient := (-8365451587509396874542972928) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 1979621752721304141969752064, coefficient := (-1979621752721304141969752064) }, { argument := 10209286764870404638519590912, coefficient := (-10209286764870404638519590912) }, { argument := 433198624683884277359706112, coefficient := (-433198624683884277359706112) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 106377060410789755818606592, coefficient := (-106377060410789755818606592) }, { argument := 16982799100825612194670444544, coefficient := (-16982799100825612194670444544) }, { argument := 169462796277929851820812795904, coefficient := (-169462796277929851820812795904) }, { argument := 16982799100825612194670444544, coefficient := (-16982799100825612194670444544) }, { argument := 106364922453189254933643264, coefficient := (-106364922453189254933643264) }, { argument := 5297658597042511054182023168, coefficient := (-5297658597042511054182023168) }, { argument := 195635484029465774815382077440, coefficient := (-195635484029465774815382077440) }, { argument := 195635436123271415391676530688, coefficient := (-195635436123271415391676530688) }, { argument := 5297706503236870477887569920, coefficient := (-5297706503236870477887569920) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 221330750011210030565556224, coefficient := (-221330750011210030565556224) }, { argument := 8173450141392774958594129920, coefficient := (-8173450141392774958594129920) }, { argument := 8173448139921042961107779584, coefficient := (-8173448139921042961107779584) }, { argument := 221332751482942028051906560, coefficient := (-221332751482942028051906560) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }] }

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

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 5445046070529441799885177166495744
def positiveArguments : Array ℕ := #[
    791, 1, 1, 1, 1, 1705,
    20405, 30525, 8855, 1705, 35365, 17765,
    1705, 20405, 1705, 20205, 15715, 2245,
    21103, 249195, 17511, 15715, 249195, 2245,
    17511, 17511, 17511, 17511, 17511, 20205,
    21103, 1385, 5817, 25207, 831, 831,
    1939, 25207, 25207, 831, 311071, 12465,
    5817, 25207, 1939, 12465, 1939, 25207,
    25207, 831, 1, 19, 29, 299,
    9, 29, 9, 9, 771, 9
  ]
def positiveCoefficients : Array ℕ := #[
    62669476548783091036493264715776, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 32979496359087083885984481280,
    789380203175568265916144680960, 590439370299784888926496358400, 685122440492002645889484062720, 32979496359087083885984481280, 684058585770741772215742627840, 687250149934524393236966932480,
    32979496359087083885984481280, 789380203175568265916144680960, 32979496359087083885984481280, 390821538965017319599012577280, 303972308083902359688120893440, 347396923524459839643566735360,
    408191385141240311581190914048, 4820132313901880275054488453120, 10838784013963146996879282143232, 303972308083902359688120893440, 4820132313901880275054488453120, 347396923524459839643566735360,
    338712000436348343652477566976, 338712000436348343652477566976, 338712000436348343652477566976, 10838784013963146996879282143232, 338712000436348343652477566976, 390821538965017319599012577280,
    408191385141240311581190914048, 26789796162660182511488860160, 450068575532691066193012850688, 975148580320830643418194509824, 32147755395192219013786632192, 514364086323075504220586115072,
    37505714627724255516084404224, 975148580320830643418194509824, 975148580320830643418194509824, 514364086323075504220586115072, 12033976436266953984160795983872, 964432661855766570413598965760,
    450068575532691066193012850688, 975148580320830643418194509824, 37505714627724255516084404224, 964432661855766570413598965760, 37505714627724255516084404224, 975148580320830643418194509824,
    975148580320830643418194509824, 32147755395192219013786632192, 4951760157141521099596496896, 5880215186605556305770840064, 4487532642409503496509325312, 46268008968291087774354767872,
    5570730176784211237046059008, 4487532642409503496509325312, 5570730176784211237046059008, 5570730176784211237046059008, 238612942572257047986806194176, 5570730176784211237046059008
  ]
def positiveScales : Array ℕ := #[
    9, 0, 0, 0, 0, 10,
    14, 14, 13, 10, 15, 14,
    10, 14, 10, 14, 13, 11,
    14, 17, 14, 13, 17, 11,
    14, 14, 14, 14, 14, 14,
    14, 10, 12, 14, 9, 9,
    10, 14, 14, 9, 18, 13,
    12, 14, 10, 13, 10, 14,
    14, 9, 0, 4, 4, 8,
    3, 4, 3, 3, 9, 3
  ]
def negativeArguments : Array ℕ := #[
    1, 55, 449, 277
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 4357548938284538567644917268480, 35573444968904687579501233700864, 21946201016451221513411674243072
  ]
def negativeScales : Array ℕ := #[
    0, 5, 8, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9627533884472051, 0, 0, 0, 0, 10735556023901392,
    14316635090145462, 14897703674503048, 13112276591639276, 10735556023901392, 15110034640852606, 14116750068218584,
    10735556023901392, 14316635090145462, 10735556023901392, 14302424731070821, 13939854651144344, 11132499729628509,
    14365160486418783, 17926915595544913, 14095973853603395, 13939854651144344, 17926915595544913, 11132499729628509,
    14095973853603395, 14095973853603395, 14095973853603395, 14095973853603395, 14095973853603395, 14302424731070821,
    14365160486418783, 10435670260936548, 12506059588827927, 14621536806247252, 9698704666765984, 9698704666765984,
    10921097087714823, 14621536806247252, 14621536806247252, 9698704666765984, 18246884378449789, 13605595262378452,
    12506059588827927, 14621536806247252, 10921097087714823, 13605595262378452, 10921097087714823, 14621536806247252,
    14621536806247252, 9698704666765984, 0, 4247927513443585, 4857980995002857, 8224001674198104,
    3169925001442312, 4857980995002857, 3169925001442312, 3169925001442312, 9590587049914763, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 5781359713964302, 8810571635541341, 8113742166049189
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 1173116501 / 62500000000
noncomputable def negativeCeiling : ℝ := 3109659209 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 62669476548783091036493264715776, coefficient := 62669476548783091036493264715776 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 789380203175568265916144680960, coefficient := 789380203175568265916144680960 }, { argument := 590439370299784888926496358400, coefficient := 590439370299784888926496358400 }, { argument := 685122440492002645889484062720, coefficient := 685122440492002645889484062720 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 684058585770741772215742627840, coefficient := 684058585770741772215742627840 }, { argument := 687250149934524393236966932480, coefficient := 687250149934524393236966932480 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 789380203175568265916144680960, coefficient := 789380203175568265916144680960 }, { argument := 32979496359087083885984481280, coefficient := 32979496359087083885984481280 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 390821538965017319599012577280, coefficient := 390821538965017319599012577280 }, { argument := 303972308083902359688120893440, coefficient := 303972308083902359688120893440 }, { argument := 347396923524459839643566735360, coefficient := 347396923524459839643566735360 }, { argument := 408191385141240311581190914048, coefficient := 408191385141240311581190914048 }, { argument := 4820132313901880275054488453120, coefficient := 4820132313901880275054488453120 }, { argument := 10838784013963146996879282143232, coefficient := 10838784013963146996879282143232 }, { argument := 303972308083902359688120893440, coefficient := 303972308083902359688120893440 }, { argument := 4820132313901880275054488453120, coefficient := 4820132313901880275054488453120 }, { argument := 347396923524459839643566735360, coefficient := 347396923524459839643566735360 }, { argument := 338712000436348343652477566976, coefficient := 338712000436348343652477566976 }, { argument := 338712000436348343652477566976, coefficient := 338712000436348343652477566976 }, { argument := 338712000436348343652477566976, coefficient := 338712000436348343652477566976 }, { argument := 10838784013963146996879282143232, coefficient := 10838784013963146996879282143232 }, { argument := 338712000436348343652477566976, coefficient := 338712000436348343652477566976 }, { argument := 390821538965017319599012577280, coefficient := 390821538965017319599012577280 }, { argument := 408191385141240311581190914048, coefficient := 408191385141240311581190914048 }, { argument := 35573444968904687579501233700864, coefficient := (-35573444968904687579501233700864) }, { argument := 26789796162660182511488860160, coefficient := 26789796162660182511488860160 }, { argument := 450068575532691066193012850688, coefficient := 450068575532691066193012850688 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 32147755395192219013786632192, coefficient := 32147755395192219013786632192 }, { argument := 514364086323075504220586115072, coefficient := 514364086323075504220586115072 }, { argument := 37505714627724255516084404224, coefficient := 37505714627724255516084404224 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 514364086323075504220586115072, coefficient := 514364086323075504220586115072 }, { argument := 12033976436266953984160795983872, coefficient := 12033976436266953984160795983872 }, { argument := 964432661855766570413598965760, coefficient := 964432661855766570413598965760 }, { argument := 450068575532691066193012850688, coefficient := 450068575532691066193012850688 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 37505714627724255516084404224, coefficient := 37505714627724255516084404224 }, { argument := 964432661855766570413598965760, coefficient := 964432661855766570413598965760 }, { argument := 37505714627724255516084404224, coefficient := 37505714627724255516084404224 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 975148580320830643418194509824, coefficient := 975148580320830643418194509824 }, { argument := 32147755395192219013786632192, coefficient := 32147755395192219013786632192 }, { argument := 21946201016451221513411674243072, coefficient := (-21946201016451221513411674243072) }, { argument := 4951760157141521099596496896, coefficient := 4951760157141521099596496896 }, { argument := 5880215186605556305770840064, coefficient := 5880215186605556305770840064 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 46268008968291087774354767872, coefficient := 46268008968291087774354767872 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 238612942572257047986806194176, coefficient := 238612942572257047986806194176 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
