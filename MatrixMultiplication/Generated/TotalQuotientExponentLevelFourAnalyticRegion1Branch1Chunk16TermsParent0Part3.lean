import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10873196556962503384457984434241536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    117108860025, 18332735231275, 4583185488775, 468442163925, 28835806835, 67515,
    55941, 107220795517, 376155, 1801858649, 1506549, 1506549,
    1078311, 55941, 7491487125, 1172750293375, 293187680875, 29966378625,
    806705941849, 122115, 101181, 2999691109367, 680355, 50408510827,
    2724909, 2724909, 1950351, 101181, 85085660707, 85085641181,
    882551348325, 385273800941085, 30827069451, 14622159901037643, 9755401725, 1170648207,
    30827069451, 61263922833, 9755401725, 945493535187, 60483490695, 1541097496762017,
    30827069451, 1170648207, 60483490695, 1170648207, 30827069451, 30827069451,
    882551348325, 1539077147797785, 2577905955, 58740675151925795, 26973698895, 1194639345,
    58740668142362735, 1194639345, 2326402935, 43950152745, 2326402935, 26973698895,
    43950152745, 1539080848286805, 2326402935, 2326402935
  ]
def negativeCoefficients : Array ℕ := #[
    1080138584822525081351828275200, 42272409372801051549015788748800, 42272424876885922975281525555200, 1080154088907396507617565081600, 1063853497688339264586876190720, 5101289169455105545642967040,
    264173903418210822899367936, 3955749148563286818937785810944, 7105367057455325581431275520, 1063629611363297570982448857088, 7114476502400781127048495104, 7114476502400781127048495104,
    5092179724509650000025747456, 264173903418210822899367936, 69096772863182578460393472000, 2704178065532052410275463168000, 2704179057332776748315574272000, 69097764663906916500504576000,
    1860137256503665364456594997248, 9226748528890027604327792640, 477813763103233572366974976, 6916816774334367213242898448384, 12851542593811109877456568320, 1859745796724972037376902692864,
    12868018930469842069607153664, 12868018930469842069607153664, 9210272192231295412177207296, 477813763103233572366974976, 196194175925564238458009944064, 196194130901673640551421837312,
    7949315846903597638248038400, 867559473176942528564381614080, 71082382588133376358562660352, 8231544235208117210306750447616, 44988849739324921745925734400, 2699330984359495304755544064,
    71082382588133376358562660352, 70632494090740127141103403008, 44988849739324921745925734400, 1090079829183842853903780544512, 69732717095953628706184888320, 867560764019877990890999906304,
    71082382588133376358562660352, 2699330984359495304755544064, 69732717095953628706184888320, 2699330984359495304755544064, 71082382588133376358562660352, 71082382588133376358562660352,
    7949315846903597638248038400, 866423408664568790547085393920, 23776985698988406025633136640, 33068060340713045484345795543040, 248788460118683565487722332160, 22037206257599010462781931520,
    33068056394679847353596583608320, 22037206257599010462781931520, 21457279777135878608498196480, 810737219687458332288661585920, 21457279777135878608498196480, 248788460118683565487722332160,
    810737219687458332288661585920, 866425491854690235623575388160, 21457279777135878608498196480, 21457279777135878608498196480
  ]
def negativeScales : Array ℕ := #[
    36, 44, 42, 38, 34, 16,
    15, 36, 18, 30, 20, 20,
    20, 15, 32, 40, 38, 34,
    39, 16, 16, 41, 19, 35,
    21, 21, 20, 16, 36, 36,
    39, 48, 34, 53, 33, 30,
    34, 35, 33, 39, 35, 50,
    34, 30, 35, 30, 34, 34,
    39, 50, 31, 55, 34, 30,
    55, 30, 31, 35, 31, 34,
    35, 50, 31, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36769059273061288, 44059487284563726, 42059487813695199, 38769079981057747, 34747142339108416, 16042920444994070,
    15771618423534793, 36641793788003512, 18520967741799253, 30746838694212556, 20522816166191654, 20522816166191654,
    20040341900892294, 15771618423534793, 32802604989226212, 40093033000386617, 38093033529518090, 34802625697222808,
    39553251926004692, 16897880903343928, 16626578877333553, 41447951086726861, 19375928195943988, 35552948283618382,
    21377776620336357, 21377776620336357, 20895302359051428, 16626578877333553, 36308196967153973, 36308196636075077,
    39682889263064047, 48452877412843968, 34843478697795297, 53699005951881702, 33183554137864329, 30124660448810760,
    34843478697795297, 35834318698261377, 33183554137864329, 39782276637989099, 35815822354252776, 50452879559430310,
    34843478697795297, 30124660448810760, 35815822354252776, 30124660448810760, 34843478697795297, 34843478697795297,
    39682889263064047, 50450986973336388, 31263552487456989, 55705209366045471, 34650834320360214, 30153927996282491,
    55705209193887721, 30153927996282491, 31115453848467855, 35355149128214343, 31115453848467855, 34650834320360214,
    35355149128214343, 50450990442084363, 31115453848467855, 31115453848467855
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
noncomputable def negativeCeiling : ℝ := 108827123277 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1080138584822525081351828275200, coefficient := (-1080138584822525081351828275200) }, { argument := 42272409372801051549015788748800, coefficient := (-42272409372801051549015788748800) }, { argument := 42272424876885922975281525555200, coefficient := (-42272424876885922975281525555200) }, { argument := 1080154088907396507617565081600, coefficient := (-1080154088907396507617565081600) }, { argument := 1063853497688339264586876190720, coefficient := (-1063853497688339264586876190720) }, { argument := 5101289169455105545642967040, coefficient := (-5101289169455105545642967040) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 3955749148563286818937785810944, coefficient := (-3955749148563286818937785810944) }, { argument := 7105367057455325581431275520, coefficient := (-7105367057455325581431275520) }, { argument := 1063629611363297570982448857088, coefficient := (-1063629611363297570982448857088) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 5092179724509650000025747456, coefficient := (-5092179724509650000025747456) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 69096772863182578460393472000, coefficient := (-69096772863182578460393472000) }, { argument := 2704178065532052410275463168000, coefficient := (-2704178065532052410275463168000) }, { argument := 2704179057332776748315574272000, coefficient := (-2704179057332776748315574272000) }, { argument := 69097764663906916500504576000, coefficient := (-69097764663906916500504576000) }, { argument := 1860137256503665364456594997248, coefficient := (-1860137256503665364456594997248) }, { argument := 9226748528890027604327792640, coefficient := (-9226748528890027604327792640) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 6916816774334367213242898448384, coefficient := (-6916816774334367213242898448384) }, { argument := 12851542593811109877456568320, coefficient := (-12851542593811109877456568320) }, { argument := 1859745796724972037376902692864, coefficient := (-1859745796724972037376902692864) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 12868018930469842069607153664, coefficient := (-12868018930469842069607153664) }, { argument := 9210272192231295412177207296, coefficient := (-9210272192231295412177207296) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 196194175925564238458009944064, coefficient := (-196194175925564238458009944064) }, { argument := 196194130901673640551421837312, coefficient := (-196194130901673640551421837312) }, { argument := 7949315846903597638248038400, coefficient := (-7949315846903597638248038400) }, { argument := 867559473176942528564381614080, coefficient := (-867559473176942528564381614080) }, { argument := 71082382588133376358562660352, coefficient := (-71082382588133376358562660352) }, { argument := 8231544235208117210306750447616, coefficient := (-8231544235208117210306750447616) }, { argument := 44988849739324921745925734400, coefficient := (-44988849739324921745925734400) }, { argument := 2699330984359495304755544064, coefficient := (-2699330984359495304755544064) }, { argument := 71082382588133376358562660352, coefficient := (-71082382588133376358562660352) }, { argument := 70632494090740127141103403008, coefficient := (-70632494090740127141103403008) }, { argument := 44988849739324921745925734400, coefficient := (-44988849739324921745925734400) }, { argument := 1090079829183842853903780544512, coefficient := (-1090079829183842853903780544512) }, { argument := 69732717095953628706184888320, coefficient := (-69732717095953628706184888320) }, { argument := 867560764019877990890999906304, coefficient := (-867560764019877990890999906304) }, { argument := 71082382588133376358562660352, coefficient := (-71082382588133376358562660352) }, { argument := 2699330984359495304755544064, coefficient := (-2699330984359495304755544064) }, { argument := 69732717095953628706184888320, coefficient := (-69732717095953628706184888320) }, { argument := 2699330984359495304755544064, coefficient := (-2699330984359495304755544064) }, { argument := 71082382588133376358562660352, coefficient := (-71082382588133376358562660352) }, { argument := 71082382588133376358562660352, coefficient := (-71082382588133376358562660352) }, { argument := 7949315846903597638248038400, coefficient := (-7949315846903597638248038400) }, { argument := 866423408664568790547085393920, coefficient := (-866423408664568790547085393920) }, { argument := 23776985698988406025633136640, coefficient := (-23776985698988406025633136640) }, { argument := 33068060340713045484345795543040, coefficient := (-33068060340713045484345795543040) }, { argument := 248788460118683565487722332160, coefficient := (-248788460118683565487722332160) }, { argument := 22037206257599010462781931520, coefficient := (-22037206257599010462781931520) }, { argument := 33068056394679847353596583608320, coefficient := (-33068056394679847353596583608320) }, { argument := 22037206257599010462781931520, coefficient := (-22037206257599010462781931520) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 810737219687458332288661585920, coefficient := (-810737219687458332288661585920) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 248788460118683565487722332160, coefficient := (-248788460118683565487722332160) }, { argument := 810737219687458332288661585920, coefficient := (-810737219687458332288661585920) }, { argument := 866425491854690235623575388160, coefficient := (-866425491854690235623575388160) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2477323691388464279931999597101056)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2577905955, 160559271379757, 3675, 3045, 74111688733201883, 20475,
    20551549111030693, 82005, 82005, 58695, 3045, 3818241825,
    597724343075, 149431140575, 15273186525, 28835806835, 67515, 55941,
    107220795517, 376155, 1801858649, 1506549, 1506549, 1078311,
    55941, 200712076031015, 200712093010905, 26022855559, 1995, 1653,
    96765778217, 11115, 1626086197, 44517, 44517, 31863,
    1653, 35884371993, 35884363751, 1, 4089, 3045,
    3219, 261, 55941, 101181, 3045, 55941,
    1653, 1653, 3219, 3219, 101181, 3219,
    4089, 261, 14311119, 586329195, 12072972165, 586329195,
    14311119, 144996525, 22698392775, 5674600275
  ]
def negativeCoefficients : Array ℕ := #[
    23776985698988406025633136640, 5784757398054015746878027595776, 277675149192735138565324800, 14379605940338069675704320, 20860585860165386688962125365248, 386761814947023943001702400,
    5784746807395267332486996164608, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 70434129757308692882207539200,
    2756516995832672779506601164800, 2756518006829540169250714419200, 70435140754176082626320793600, 1063853497688339264586876190720, 5101289169455105545642967040, 264173903418210822899367936,
    3955749148563286818937785810944, 7105367057455325581431275520, 1063629611363297570982448857088, 7114476502400781127048495104, 7114476502400781127048495104, 5092179724509650000025747456,
    264173903418210822899367936, 451963415411018907876295966720, 451963453646332046272301629440, 60004619570497863877727879168, 301475876266398150442352640, 15612143592367047076478976,
    223126693232792196518546243584, 419912827656768852401848320, 59991991835701304939673288704, 420451177435815991956209664, 420451177435815991956209664, 300937526487351010887991296,
    15612143592367047076478976, 165487456600165440406444572672, 165487418590649276527913467904, 19807040628566084398385987584, 19309756548453979278802944, 14379605940338069675704320,
    15201297708357387942887424, 19720602432463638412394496, 264173903418210822899367936, 477813763103233572366974976, 14379605940338069675704320, 264173903418210822899367936,
    15612143592367047076478976, 15612143592367047076478976, 15201297708357387942887424, 15201297708357387942887424, 477813763103233572366974976, 15201297708357387942887424,
    19309756548453979278802944, 19720602432463638412394496, 131996774800701082306609152, 21631729206218284125640458240, 222707027736774124954598768640, 21631729206218284125640458240,
    131996774800701082306609152, 2674713788252228843628134400, 104677860601240738462275993600, 104677898993526841870280294400
  ]
def negativeScales : Array ℕ := #[
    31, 47, 11, 11, 56, 14,
    54, 16, 16, 15, 11, 31,
    39, 37, 33, 34, 16, 15,
    36, 18, 30, 20, 20, 20,
    15, 47, 47, 34, 10, 10,
    36, 13, 30, 15, 15, 14,
    10, 35, 35, 0, 11, 11,
    11, 8, 15, 16, 11, 15,
    10, 10, 11, 11, 16, 11,
    11, 8, 23, 29, 33, 29,
    23, 27, 34, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31263552487456989, 47190099303280608, 11843528536141147, 11572226512796267, 56040550617375805, 14321575831415734,
    54190096662010838, 16323424255808103, 16323424255808103, 15840949991965165, 11572226512796267, 31830261332630486,
    39120689343289482, 37120689872420956, 33830282040627275, 34747142339108416, 16042920444994070, 15771618423534793,
    36641793788003512, 18520967741799253, 30746838694212556, 20522816166191654, 20522816166191654, 20040341900892294,
    15771618423534793, 47512120748840709, 47512120870890177, 34599060230487762, 10962173043893966, 10690871009350625,
    36493777869040322, 13440220327914385, 30598756589072806, 15442068752306756, 15442068752306756, 14959594499254218,
    10690871009350625, 35062636621415309, 35062636290053960, 0, 11997532370288072, 11572226512796267,
    11652396861500322, 8027905996569885, 15771618423534793, 16626578877333553, 11572226512796267, 15771618423534793,
    10690871009350625, 10690871009350625, 11652396861500322, 11652396861500322, 16626578877333553, 11652396861500322,
    11997532370288072, 8027905996569885, 23770633146734048, 29127135653515491, 33491061836222321, 29127135653515491,
    23770633146734048, 27111443083991923, 34401871095833543, 32401871624965016
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
noncomputable def negativeCeiling : ℝ := 13654447301 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23776985698988406025633136640, coefficient := (-23776985698988406025633136640) }, { argument := 5784757398054015746878027595776, coefficient := (-5784757398054015746878027595776) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 20860585860165386688962125365248, coefficient := (-20860585860165386688962125365248) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 5784746807395267332486996164608, coefficient := (-5784746807395267332486996164608) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 70434129757308692882207539200, coefficient := (-70434129757308692882207539200) }, { argument := 2756516995832672779506601164800, coefficient := (-2756516995832672779506601164800) }, { argument := 2756518006829540169250714419200, coefficient := (-2756518006829540169250714419200) }, { argument := 70435140754176082626320793600, coefficient := (-70435140754176082626320793600) }, { argument := 1063853497688339264586876190720, coefficient := (-1063853497688339264586876190720) }, { argument := 5101289169455105545642967040, coefficient := (-5101289169455105545642967040) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 3955749148563286818937785810944, coefficient := (-3955749148563286818937785810944) }, { argument := 7105367057455325581431275520, coefficient := (-7105367057455325581431275520) }, { argument := 1063629611363297570982448857088, coefficient := (-1063629611363297570982448857088) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 7114476502400781127048495104, coefficient := (-7114476502400781127048495104) }, { argument := 5092179724509650000025747456, coefficient := (-5092179724509650000025747456) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 451963415411018907876295966720, coefficient := (-451963415411018907876295966720) }, { argument := 451963453646332046272301629440, coefficient := (-451963453646332046272301629440) }, { argument := 60004619570497863877727879168, coefficient := (-60004619570497863877727879168) }, { argument := 301475876266398150442352640, coefficient := (-301475876266398150442352640) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 223126693232792196518546243584, coefficient := (-223126693232792196518546243584) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 59991991835701304939673288704, coefficient := (-59991991835701304939673288704) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 420451177435815991956209664, coefficient := (-420451177435815991956209664) }, { argument := 300937526487351010887991296, coefficient := (-300937526487351010887991296) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 165487456600165440406444572672, coefficient := (-165487456600165440406444572672) }, { argument := 165487418590649276527913467904, coefficient := (-165487418590649276527913467904) }, { argument := 19807040628566084398385987584, coefficient := (-19807040628566084398385987584) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 264173903418210822899367936, coefficient := (-264173903418210822899367936) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 15612143592367047076478976, coefficient := (-15612143592367047076478976) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 477813763103233572366974976, coefficient := (-477813763103233572366974976) }, { argument := 15201297708357387942887424, coefficient := (-15201297708357387942887424) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 19720602432463638412394496, coefficient := (-19720602432463638412394496) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 222707027736774124954598768640, coefficient := (-222707027736774124954598768640) }, { argument := 21631729206218284125640458240, coefficient := (-21631729206218284125640458240) }, { argument := 131996774800701082306609152, coefficient := (-131996774800701082306609152) }, { argument := 2674713788252228843628134400, coefficient := (-2674713788252228843628134400) }, { argument := 104677860601240738462275993600, coefficient := (-104677860601240738462275993600) }, { argument := 104677898993526841870280294400, coefficient := (-104677898993526841870280294400) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
