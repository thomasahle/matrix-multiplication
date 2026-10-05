import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17543695744347974837368019132350464)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    937531, 117755585, 26651, 3829134701, 27257, 109,
    26651, 15233, 27257, 426269, 4197, 117755641,
    26651, 109, 4197, 109, 3353, 15233,
    7504339, 480506420456061, 27401394565, 16012428420034947, 678038763385, 21571310615,
    32024816624302725, 11077159505, 11077159505, 374874397985, 20405293825, 678038763385,
    374874397985, 961058551217531, 21571310615, 20405293825, 27401394565, 4755784565386847,
    12157585005, 3967211949, 8095554048822001, 40056043227, 4755784330689727, 80240061033,
    35960856699, 12157585005, 3967211949, 35179535, 1299133425, 10393064855,
    281438825, 12157585005, 22109878675, 12157585005, 481829412612733, 35179535,
    481825066857859, 17762555, 3967211949, 7214802515, 3967211949, 13996395785,
    13996389111, 7406603, 480502074996099, 27401381499
  ]
def negativeCoefficients : Array ℕ := #[
    35418919768410090774732996608, 2224340111098830203524889968640, 515505312296791714161508745216, 18082577370395480547321914064896, 527227057043775158639459827712, 16866933035263306245500567552,
    515505312296791714161508745216, 294649072163034339492786864128, 527227057043775158639459827712, 8245241603220933818765230997504, 324727146555046313359476523008, 2224341168908922366325417836544,
    515505312296791714161508745216, 16866933035263306245500567552, 324727146555046313359476523008, 16866933035263306245500567552, 518851618965485007717095440384, 294649072163034339492786864128,
    35438238969691510493302226944, 2164008536115047196242535776256, 126366628200822716759812341760, 72113566665766127316074036723712, 3126901885054400416843867095040, 99480111562349798300277800960,
    72113476107909108952560618700800, 102168763226197090146231255040, 102168763226197090146231255040, 1728803019853808656948070973440, 94102808234655214608370892800, 3126901885054400416843867095040,
    1728803019853808656948070973440, 2164111466572250678226413682688, 99480111562349798300277800960, 94102808234655214608370892800, 126366628200822716759812341760, 21418149596530560418243634266112,
    112133929570801929725977559040, 4573883969335341870401716224, 72918268395264947771731966164992, 92362947251739484221660463104, 21418148539548698241315050094592, 92510491895911592023931486208,
    82920090024724584876314984448, 112133929570801929725977559040, 4573883969335341870401716224, 1297895757554215501818757120, 47929563617153484492216729600, 47929551880412567594514513920,
    1297907494295132399520972800, 112133929570801929725977559040, 407855273418493443418410188800, 112133929570801929725977559040, 2169966763098849304305958125568, 1297895757554215501818757120,
    2169947191558818114389162328064, 1310645224720759858418155520, 4573883969335341870401716224, 16636201942070127297329889280, 4573883969335341870401716224, 129093965500121048776211169280,
    129093903943336074807437426688, 34976693759121762848696434688, 2163988965903181579632827695104, 126366567944533199987561988096
  ]
def negativeScales : Array ℕ := #[
    19, 26, 14, 31, 14, 6,
    14, 13, 14, 18, 12, 26,
    14, 6, 12, 6, 11, 13,
    22, 48, 34, 53, 39, 34,
    54, 33, 33, 38, 34, 39,
    38, 49, 34, 34, 34, 52,
    33, 31, 52, 35, 52, 36,
    35, 33, 31, 25, 30, 33,
    28, 33, 34, 33, 48, 25,
    48, 24, 31, 32, 31, 33,
    33, 22, 48, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19838506870648658, 26811220246590304, 14701902046492302, 31834371267361396, 14734339162567138, 6768184325109843,
    14701902046492302, 13894912478932703, 14734339162567138, 18701404615029368, 12035142747885910, 26811220932680093,
    14701902046492302, 6768184325109843, 12035142747885910, 6768184325109843, 11711236767887864, 13894912478932703,
    22839293572171125, 48771549036987256, 34673530268404747, 53830041640712505, 39302576798161987, 34328394782317719,
    54830039829022107, 33366868930132356, 33366868930132356, 38447616344016759, 34248224433633735, 39302576798161987,
    38447616344016759, 49771617656739585, 34328394782317719, 34248224433633735, 34673530268404747, 52078604786525289,
    33501137627710497, 31885478333124769, 52846051244929817, 35221300866311886, 52078604715328544, 36223603652181307,
    35065708339600194, 33501137627710497, 31885478333124769, 25068233077731256, 30274902461600965, 33274902108321304,
    28068246123818555, 33501137627710497, 34363972057453541, 33501137627710497, 48775515792407753, 25068233077731256,
    48775502780276972, 24082335780849439, 31885478333124769, 32748312759726197, 31885478333124769, 33704336315227715,
    33704335627297111, 22820380579933424, 48771535989915113, 34673529580474143
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
noncomputable def negativeCeiling : ℝ := 23812754201 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35418919768410090774732996608, coefficient := (-35418919768410090774732996608) }, { argument := 2224340111098830203524889968640, coefficient := (-2224340111098830203524889968640) }, { argument := 515505312296791714161508745216, coefficient := (-515505312296791714161508745216) }, { argument := 18082577370395480547321914064896, coefficient := (-18082577370395480547321914064896) }, { argument := 527227057043775158639459827712, coefficient := (-527227057043775158639459827712) }, { argument := 16866933035263306245500567552, coefficient := (-16866933035263306245500567552) }, { argument := 515505312296791714161508745216, coefficient := (-515505312296791714161508745216) }, { argument := 294649072163034339492786864128, coefficient := (-294649072163034339492786864128) }, { argument := 527227057043775158639459827712, coefficient := (-527227057043775158639459827712) }, { argument := 8245241603220933818765230997504, coefficient := (-8245241603220933818765230997504) }, { argument := 324727146555046313359476523008, coefficient := (-324727146555046313359476523008) }, { argument := 2224341168908922366325417836544, coefficient := (-2224341168908922366325417836544) }, { argument := 515505312296791714161508745216, coefficient := (-515505312296791714161508745216) }, { argument := 16866933035263306245500567552, coefficient := (-16866933035263306245500567552) }, { argument := 324727146555046313359476523008, coefficient := (-324727146555046313359476523008) }, { argument := 16866933035263306245500567552, coefficient := (-16866933035263306245500567552) }, { argument := 518851618965485007717095440384, coefficient := (-518851618965485007717095440384) }, { argument := 294649072163034339492786864128, coefficient := (-294649072163034339492786864128) }, { argument := 35438238969691510493302226944, coefficient := (-35438238969691510493302226944) }, { argument := 2164008536115047196242535776256, coefficient := (-2164008536115047196242535776256) }, { argument := 126366628200822716759812341760, coefficient := (-126366628200822716759812341760) }, { argument := 72113566665766127316074036723712, coefficient := (-72113566665766127316074036723712) }, { argument := 3126901885054400416843867095040, coefficient := (-3126901885054400416843867095040) }, { argument := 99480111562349798300277800960, coefficient := (-99480111562349798300277800960) }, { argument := 72113476107909108952560618700800, coefficient := (-72113476107909108952560618700800) }, { argument := 102168763226197090146231255040, coefficient := (-102168763226197090146231255040) }, { argument := 102168763226197090146231255040, coefficient := (-102168763226197090146231255040) }, { argument := 1728803019853808656948070973440, coefficient := (-1728803019853808656948070973440) }, { argument := 94102808234655214608370892800, coefficient := (-94102808234655214608370892800) }, { argument := 3126901885054400416843867095040, coefficient := (-3126901885054400416843867095040) }, { argument := 1728803019853808656948070973440, coefficient := (-1728803019853808656948070973440) }, { argument := 2164111466572250678226413682688, coefficient := (-2164111466572250678226413682688) }, { argument := 99480111562349798300277800960, coefficient := (-99480111562349798300277800960) }, { argument := 94102808234655214608370892800, coefficient := (-94102808234655214608370892800) }, { argument := 126366628200822716759812341760, coefficient := (-126366628200822716759812341760) }, { argument := 21418149596530560418243634266112, coefficient := (-21418149596530560418243634266112) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 72918268395264947771731966164992, coefficient := (-72918268395264947771731966164992) }, { argument := 92362947251739484221660463104, coefficient := (-92362947251739484221660463104) }, { argument := 21418148539548698241315050094592, coefficient := (-21418148539548698241315050094592) }, { argument := 92510491895911592023931486208, coefficient := (-92510491895911592023931486208) }, { argument := 82920090024724584876314984448, coefficient := (-82920090024724584876314984448) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 1297895757554215501818757120, coefficient := (-1297895757554215501818757120) }, { argument := 47929563617153484492216729600, coefficient := (-47929563617153484492216729600) }, { argument := 47929551880412567594514513920, coefficient := (-47929551880412567594514513920) }, { argument := 1297907494295132399520972800, coefficient := (-1297907494295132399520972800) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 407855273418493443418410188800, coefficient := (-407855273418493443418410188800) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 2169966763098849304305958125568, coefficient := (-2169966763098849304305958125568) }, { argument := 1297895757554215501818757120, coefficient := (-1297895757554215501818757120) }, { argument := 2169947191558818114389162328064, coefficient := (-2169947191558818114389162328064) }, { argument := 1310645224720759858418155520, coefficient := (-1310645224720759858418155520) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 129093965500121048776211169280, coefficient := (-129093965500121048776211169280) }, { argument := 129093903943336074807437426688, coefficient := (-129093903943336074807437426688) }, { argument := 34976693759121762848696434688, coefficient := (-34976693759121762848696434688) }, { argument := 2163988965903181579632827695104, coefficient := (-2163988965903181579632827695104) }, { argument := 126366567944533199987561988096, coefficient := (-126366567944533199987561988096) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-51650127344635532875408673836367872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16012265652809341, 678038440071, 21571300329, 32024491114470779, 11077154223, 11077154223,
    374874219231, 20405284095, 678038440071, 374874219231, 961049835678341, 21571300329,
    20405284095, 27401381499, 32382232636573669, 22109878675, 7214802515, 55132213521797851,
    72846231845, 32382231025225317, 145925199255, 65398693765, 22109878675, 7214802515,
    16038588924390787, 1299133425, 16038426156937853, 655947525, 40056043227, 72846231845,
    40056043227, 346336346765, 346336181619, 474262195, 11018439235, 11018433981,
    6395, 9511568661765469, 12157585005, 3967211949, 16191107292632387, 40056043227,
    9511568192371229, 80240061033, 35960856699, 12157585005, 3967211949, 32077137650840197,
    10393064855, 32076812140553595, 5247578915, 1956921553, 5658117445, 5658114747,
    13079, 837, 17762555, 655947525, 5247578915, 142101725,
    80240061033, 145925199255, 80240061033, 5658117445
  ]
def negativeCoefficients : Array ℕ := #[
    72112833627349540005019056603136, 3126900394031747055011374301184, 99480064126547412756165820416, 72112743124930180233373199368192, 102168714508345991479305437184, 102168714508345991479305437184,
    1728802195496486118978773581824, 94102763362950255309886586880, 3126900394031747055011374301184, 1728802195496486118978773581824, 2164091840922726469749144813568, 99480064126547412756165820416,
    94102763362950255309886586880, 126366567944533199987561988096, 72918305417748944964670730534912, 407855273418493443418410188800, 16636201942070127297329889280, 248293416272879422713973593604096,
    335943948894706441552532602880, 72918301789315026149039319023616, 336480600570257090820188405760, 301598241659464888422561218560, 407855273418493443418410188800, 16636201942070127297329889280,
    72231383103434912577567538020352, 47929563617153484492216729600, 72230650063994530970421677785088, 48400384477832791805499801600, 92362947251739484221660463104, 335943948894706441552532602880,
    92362947251739484221660463104, 3194388976098739994185821061120, 3194387452895741595767015473152, 2239639893760187837918709022720, 101627164329882527759996026880, 101627115870285846125003931648,
    494789159451875428623743713280, 21418148540417926746394761101312, 112133929570801929725977559040, 4573883969335341870401716224, 72918264769814938428810777853952, 92362947251739484221660463104,
    21418147483436064569466176929792, 92510491895911592023931486208, 82920090024724584876314984448, 112133929570801929725977559040, 4573883969335341870401716224, 72231292585718009318446104313856,
    47929551880412567594514513920, 72230559601715286303167804866560, 48400372625799724447112888320, 18482601502984828016289986379776, 104373844446906379861617541120, 104373794677590868993247281152,
    505969305431671519231426428928, 16189934576279113907665108992, 1310645224720759858418155520, 48400384477832791805499801600, 48400372625799724447112888320, 1310657076753827216805068800,
    92510491895911592023931486208, 336480600570257090820188405760, 92510491895911592023931486208, 104373844446906379861617541120
  ]
def negativeScales : Array ℕ := #[
    53, 39, 34, 54, 33, 33,
    38, 34, 39, 38, 49, 34,
    34, 34, 54, 34, 32, 55,
    36, 54, 37, 35, 34, 32,
    53, 30, 53, 29, 35, 36,
    35, 38, 38, 28, 33, 33,
    12, 53, 33, 31, 53, 35,
    53, 36, 35, 33, 31, 54,
    33, 54, 32, 30, 32, 32,
    13, 9, 24, 29, 32, 27,
    36, 37, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    53830026975562288, 39302576110231384, 34328394094387115, 54830025164962566, 33366868242201752, 33366868242201752,
    38447615656086155, 34248223745703132, 39302576110231384, 38447615656086155, 49771604573330399, 34328394094387115,
    34248223745703132, 34673529580474143, 54846051977423104, 34363972057453541, 32748312759726197, 55613745044046677,
    36084135296055210, 54846051905634218, 37086438081924631, 35928542776565779, 34363972057453541, 32748312759726197,
    53832396738447253, 30274902461600965, 53832382097196985, 29289005164719148, 35221300866311886, 36084135296055210,
    35221300866311886, 38333382844943162, 38333382157012559, 28821109631118675, 33359200829098894, 33359200141168291,
    12642728643786688, 53078604715387094, 33501137627710497, 31885478333124769, 53846051173199931, 35221300866311886,
    53078604644190346, 36223603652181307, 35065708339600194, 33501137627710497, 31885478333124769, 54832394930513628,
    33274902108321304, 54832380290352295, 32289004811439487, 30865938780219125, 32397674976913535, 32397674288982931,
    13674964618422665, 9709083812639846, 24082335780849439, 29289005164719148, 32289004811439487, 27082348826936738,
    36223603652181307, 37086438081924631, 36223603652181307, 32397674976913535
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
noncomputable def negativeCeiling : ℝ := 63905613657 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 72112833627349540005019056603136, coefficient := (-72112833627349540005019056603136) }, { argument := 3126900394031747055011374301184, coefficient := (-3126900394031747055011374301184) }, { argument := 99480064126547412756165820416, coefficient := (-99480064126547412756165820416) }, { argument := 72112743124930180233373199368192, coefficient := (-72112743124930180233373199368192) }, { argument := 102168714508345991479305437184, coefficient := (-102168714508345991479305437184) }, { argument := 102168714508345991479305437184, coefficient := (-102168714508345991479305437184) }, { argument := 1728802195496486118978773581824, coefficient := (-1728802195496486118978773581824) }, { argument := 94102763362950255309886586880, coefficient := (-94102763362950255309886586880) }, { argument := 3126900394031747055011374301184, coefficient := (-3126900394031747055011374301184) }, { argument := 1728802195496486118978773581824, coefficient := (-1728802195496486118978773581824) }, { argument := 2164091840922726469749144813568, coefficient := (-2164091840922726469749144813568) }, { argument := 99480064126547412756165820416, coefficient := (-99480064126547412756165820416) }, { argument := 94102763362950255309886586880, coefficient := (-94102763362950255309886586880) }, { argument := 126366567944533199987561988096, coefficient := (-126366567944533199987561988096) }, { argument := 72918305417748944964670730534912, coefficient := (-72918305417748944964670730534912) }, { argument := 407855273418493443418410188800, coefficient := (-407855273418493443418410188800) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 248293416272879422713973593604096, coefficient := (-248293416272879422713973593604096) }, { argument := 335943948894706441552532602880, coefficient := (-335943948894706441552532602880) }, { argument := 72918301789315026149039319023616, coefficient := (-72918301789315026149039319023616) }, { argument := 336480600570257090820188405760, coefficient := (-336480600570257090820188405760) }, { argument := 301598241659464888422561218560, coefficient := (-301598241659464888422561218560) }, { argument := 407855273418493443418410188800, coefficient := (-407855273418493443418410188800) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 72231383103434912577567538020352, coefficient := (-72231383103434912577567538020352) }, { argument := 47929563617153484492216729600, coefficient := (-47929563617153484492216729600) }, { argument := 72230650063994530970421677785088, coefficient := (-72230650063994530970421677785088) }, { argument := 48400384477832791805499801600, coefficient := (-48400384477832791805499801600) }, { argument := 92362947251739484221660463104, coefficient := (-92362947251739484221660463104) }, { argument := 335943948894706441552532602880, coefficient := (-335943948894706441552532602880) }, { argument := 92362947251739484221660463104, coefficient := (-92362947251739484221660463104) }, { argument := 3194388976098739994185821061120, coefficient := (-3194388976098739994185821061120) }, { argument := 3194387452895741595767015473152, coefficient := (-3194387452895741595767015473152) }, { argument := 2239639893760187837918709022720, coefficient := (-2239639893760187837918709022720) }, { argument := 101627164329882527759996026880, coefficient := (-101627164329882527759996026880) }, { argument := 101627115870285846125003931648, coefficient := (-101627115870285846125003931648) }, { argument := 494789159451875428623743713280, coefficient := (-494789159451875428623743713280) }, { argument := 21418148540417926746394761101312, coefficient := (-21418148540417926746394761101312) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 72918264769814938428810777853952, coefficient := (-72918264769814938428810777853952) }, { argument := 92362947251739484221660463104, coefficient := (-92362947251739484221660463104) }, { argument := 21418147483436064569466176929792, coefficient := (-21418147483436064569466176929792) }, { argument := 92510491895911592023931486208, coefficient := (-92510491895911592023931486208) }, { argument := 82920090024724584876314984448, coefficient := (-82920090024724584876314984448) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 72231292585718009318446104313856, coefficient := (-72231292585718009318446104313856) }, { argument := 47929551880412567594514513920, coefficient := (-47929551880412567594514513920) }, { argument := 72230559601715286303167804866560, coefficient := (-72230559601715286303167804866560) }, { argument := 48400372625799724447112888320, coefficient := (-48400372625799724447112888320) }, { argument := 18482601502984828016289986379776, coefficient := (-18482601502984828016289986379776) }, { argument := 104373844446906379861617541120, coefficient := (-104373844446906379861617541120) }, { argument := 104373794677590868993247281152, coefficient := (-104373794677590868993247281152) }, { argument := 505969305431671519231426428928, coefficient := (-505969305431671519231426428928) }, { argument := 16189934576279113907665108992, coefficient := (-16189934576279113907665108992) }, { argument := 1310645224720759858418155520, coefficient := (-1310645224720759858418155520) }, { argument := 48400384477832791805499801600, coefficient := (-48400384477832791805499801600) }, { argument := 48400372625799724447112888320, coefficient := (-48400372625799724447112888320) }, { argument := 1310657076753827216805068800, coefficient := (-1310657076753827216805068800) }, { argument := 92510491895911592023931486208, coefficient := (-92510491895911592023931486208) }, { argument := 336480600570257090820188405760, coefficient := (-336480600570257090820188405760) }, { argument := 92510491895911592023931486208, coefficient := (-92510491895911592023931486208) }, { argument := 104373844446906379861617541120, coefficient := (-104373844446906379861617541120) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11
