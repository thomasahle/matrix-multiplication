import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

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
def constantNumerator : ℤ := (-4407387802524931620467097642991616)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    723763143, 342176627097, 12988751931243, 1368707447121, 723763143, 24716143523,
    15785, 949779764317, 178145, 15785, 949779764317, 15785,
    15785, 654401, 4059, 178145, 654401, 24716143523,
    15785, 4059, 15785, 46361001, 21918290679, 832000837701,
    87673222847, 46361001, 44676720811, 441595, 1717848670037, 4983715,
    441595, 1717848670037, 441595, 441595, 18307267, 113553,
    4983715, 18307267, 44676720811, 441595, 113553, 441595,
    21198285971, 157251579887, 42388354795, 44413853783019, 2822845636488213, 1431350911,
    116041913, 24871361017, 44956209809, 2822833766448655, 24871361017, 734278057,
    734643113, 1431350911, 1430620799, 44956209809, 1430620799, 44413761667569,
    116041913, 2926260966461, 224741224651743, 87008357975
  ]
def negativeCoefficients : Array ℕ := #[
    26702146937809297493433778176, 3156022334031753962397552869376, 29950022839067537961921948942336, 3156024498602679530596117512192, 26702146937809297493433778176, 113983093514463742189258145792,
    2385361757827115190342123520, 4380086059685968602439056621568, 26920511266906014291003965440, 2385361757827115190342123520, 4380086059685968602439056621568, 2385361757827115190342123520,
    2385361757827115190342123520, 98890283160204118319612035072, 2453514950907889910066184192, 26920511266906014291003965440, 98890283160204118319612035072, 113983093514463742189258145792,
    2385361757827115190342123520, 2453514950907889910066184192, 2385361757827115190342123520, 1710419040895985192357855232, 202160549344343277069121093632, 1918463315272788029384637284352,
    202160687996989264097752121344, 1710419040895985192357855232, 206035008713272610663006470144, 4170746854005641956284170240, 7922178693383716185142301032448, 47069857352349387792349921280,
    4170746854005641956284170240, 7922178693383716185142301032448, 4170746854005641956284170240, 4170746854005641956284170240, 172907248147491042244809457664, 4289911049834374583606575104,
    47069857352349387792349921280, 172907248147491042244809457664, 206035008713272610663006470144, 4170746854005641956284170240, 4289911049834374583606575104, 4170746854005641956284170240,
    195519678054172288975076589568, 725194912340495343094593486848, 195481783152241026419843399680, 12501388459205753906569150464, 794560409788296667102055497728, 6600940983722004463740780544,
    8562381883738677503571525632, 114698907861358879160682938368, 207323924217653490844052750336, 794557068669188524486615367680, 114698907861358879160682938368, 6772519698209857171468845056,
    6775886745512143228506210304, 6600940983722004463740780544, 6597573936419718406703415296, 207323924217653490844052750336, 6597573936419718406703415296, 12501362531011610464971915264,
    8562381883738677503571525632, 26357415596285174186153869312, 4048577982385514817873732698112, 200627613979816306647708467200
  ]
def negativeScales : Array ℕ := #[
    29, 38, 43, 40, 29, 34,
    13, 39, 17, 13, 39, 13,
    13, 19, 11, 17, 19, 34,
    13, 11, 13, 25, 34, 39,
    36, 25, 35, 18, 40, 22,
    18, 40, 18, 18, 24, 16,
    22, 24, 35, 18, 16, 18,
    34, 37, 35, 45, 51, 30,
    26, 34, 35, 51, 34, 29,
    29, 30, 30, 35, 30, 45,
    26, 41, 47, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29430942400706854, 38315950261440825, 43562328044684382, 40315951250918826, 29430942400706854, 34524734604969423,
    13946266649986186, 39788802063230556, 17442692466319882, 13946266649986186, 39788802063230556, 13946266649986186,
    13946266649986186, 19319815427322126, 11986908643884053, 17442692466319882, 19319815427322126, 34524734604969423,
    13946266649986186, 11986908643884053, 13946266649986186, 25466408380731704, 34351416241465613, 39597794024712565,
    36351417230943614, 25466408380731704, 35378804247422635, 18752364311834874, 40643740089809230, 22248790137717588,
    18752364311834874, 40643740089809230, 18752364311834874, 18752364311834874, 24125913098719867, 16793006296655241,
    22248790137717588, 24125913098719867, 35378804247422635, 18752364311834874, 16793006296655241, 18752364311834874,
    34303228566440026, 37194283555515409, 35302948921514435, 45336074992691002, 51326071662419739, 30414730261548542,
    26790070743908151, 34533766406117671, 35387801358092243, 51326065595887801, 34533766406117671, 29451751246542395,
    29452468323132271, 30414730261548542, 30413994175317596, 35387801358092243, 30413994175317596, 45336072000502092,
    26790070743908151, 41412195574642377, 47675258113174645, 36340434940983530
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
noncomputable def negativeCeiling : ℝ := 7281841371 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 26702146937809297493433778176, coefficient := (-26702146937809297493433778176) }, { argument := 3156022334031753962397552869376, coefficient := (-3156022334031753962397552869376) }, { argument := 29950022839067537961921948942336, coefficient := (-29950022839067537961921948942336) }, { argument := 3156024498602679530596117512192, coefficient := (-3156024498602679530596117512192) }, { argument := 26702146937809297493433778176, coefficient := (-26702146937809297493433778176) }, { argument := 113983093514463742189258145792, coefficient := (-113983093514463742189258145792) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 4380086059685968602439056621568, coefficient := (-4380086059685968602439056621568) }, { argument := 26920511266906014291003965440, coefficient := (-26920511266906014291003965440) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 4380086059685968602439056621568, coefficient := (-4380086059685968602439056621568) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 98890283160204118319612035072, coefficient := (-98890283160204118319612035072) }, { argument := 2453514950907889910066184192, coefficient := (-2453514950907889910066184192) }, { argument := 26920511266906014291003965440, coefficient := (-26920511266906014291003965440) }, { argument := 98890283160204118319612035072, coefficient := (-98890283160204118319612035072) }, { argument := 113983093514463742189258145792, coefficient := (-113983093514463742189258145792) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 2453514950907889910066184192, coefficient := (-2453514950907889910066184192) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 1710419040895985192357855232, coefficient := (-1710419040895985192357855232) }, { argument := 202160549344343277069121093632, coefficient := (-202160549344343277069121093632) }, { argument := 1918463315272788029384637284352, coefficient := (-1918463315272788029384637284352) }, { argument := 202160687996989264097752121344, coefficient := (-202160687996989264097752121344) }, { argument := 1710419040895985192357855232, coefficient := (-1710419040895985192357855232) }, { argument := 206035008713272610663006470144, coefficient := (-206035008713272610663006470144) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 7922178693383716185142301032448, coefficient := (-7922178693383716185142301032448) }, { argument := 47069857352349387792349921280, coefficient := (-47069857352349387792349921280) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 7922178693383716185142301032448, coefficient := (-7922178693383716185142301032448) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 172907248147491042244809457664, coefficient := (-172907248147491042244809457664) }, { argument := 4289911049834374583606575104, coefficient := (-4289911049834374583606575104) }, { argument := 47069857352349387792349921280, coefficient := (-47069857352349387792349921280) }, { argument := 172907248147491042244809457664, coefficient := (-172907248147491042244809457664) }, { argument := 206035008713272610663006470144, coefficient := (-206035008713272610663006470144) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 4289911049834374583606575104, coefficient := (-4289911049834374583606575104) }, { argument := 4170746854005641956284170240, coefficient := (-4170746854005641956284170240) }, { argument := 195519678054172288975076589568, coefficient := (-195519678054172288975076589568) }, { argument := 725194912340495343094593486848, coefficient := (-725194912340495343094593486848) }, { argument := 195481783152241026419843399680, coefficient := (-195481783152241026419843399680) }, { argument := 12501388459205753906569150464, coefficient := (-12501388459205753906569150464) }, { argument := 794560409788296667102055497728, coefficient := (-794560409788296667102055497728) }, { argument := 6600940983722004463740780544, coefficient := (-6600940983722004463740780544) }, { argument := 8562381883738677503571525632, coefficient := (-8562381883738677503571525632) }, { argument := 114698907861358879160682938368, coefficient := (-114698907861358879160682938368) }, { argument := 207323924217653490844052750336, coefficient := (-207323924217653490844052750336) }, { argument := 794557068669188524486615367680, coefficient := (-794557068669188524486615367680) }, { argument := 114698907861358879160682938368, coefficient := (-114698907861358879160682938368) }, { argument := 6772519698209857171468845056, coefficient := (-6772519698209857171468845056) }, { argument := 6775886745512143228506210304, coefficient := (-6775886745512143228506210304) }, { argument := 6600940983722004463740780544, coefficient := (-6600940983722004463740780544) }, { argument := 6597573936419718406703415296, coefficient := (-6597573936419718406703415296) }, { argument := 207323924217653490844052750336, coefficient := (-207323924217653490844052750336) }, { argument := 6597573936419718406703415296, coefficient := (-6597573936419718406703415296) }, { argument := 12501362531011610464971915264, coefficient := (-12501362531011610464971915264) }, { argument := 8562381883738677503571525632, coefficient := (-8562381883738677503571525632) }, { argument := 26357415596285174186153869312, coefficient := (-26357415596285174186153869312) }, { argument := 4048577982385514817873732698112, coefficient := (-4048577982385514817873732698112) }, { argument := 200627613979816306647708467200, coefficient := (-200627613979816306647708467200) }] }

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
def constantNumerator : ℤ := (-6991804594348994453459226073235456)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    285061915641411, 3389936025, 5649893375, 172886737275, 5649893375, 3389936025,
    2769577732425, 177406651975, 56185387272259, 172886737275, 5649893375, 177406651975,
    5649893375, 172886737275, 5649893375, 2926260966461, 706483309759583, 13475,
    111237594327709781, 152075, 13475, 27809403947904233, 13475, 13475,
    558635, 3465, 152075, 558635, 2825962309984907, 13475,
    3465, 13475, 45179829, 21359862891, 810803364129, 85439510163,
    45179829, 24716143523, 15785, 949779764317, 178145, 15785,
    949779764317, 15785, 15785, 654401, 4059, 178145,
    654401, 24716143523, 15785, 4059, 15785, 1463828469299331,
    5278986821880801, 366032324796135, 729719603, 14245, 28064434381, 160765,
    14245, 28064434381, 14245, 14245
  ]
def negativeCoefficients : Array ℕ := #[
    41081751585925707035237670715392, 125066564558846528819350732800, 6513883570773256709341184000, 199324837265661655305840230400, 208444274264744214698917888000, 125066564558846528819350732800,
    3193105726393050438919048396800, 204535944122280260673313177600, 4048583826928202257443453927424, 199324837265661655305840230400, 6513883570773256709341184000, 204535944122280260673313177600,
    6513883570773256709341184000, 199324837265661655305840230400, 208444274264744214698917888000, 26357415596285174186153869312, 795429492644183174702056865792, 127267776713336938509107200,
    31310599272741510576493178126336, 1436307765764802591745638400, 127267776713336938509107200, 31310605314294276023900954427392, 127267776713336938509107200, 127267776713336938509107200,
    5276158400315768507906129920, 130903998905146565323653120, 1436307765764802591745638400, 5276158400315768507906129920, 795437675388193329551866068992, 127267776713336938509107200,
    130903998905146565323653120, 127267776713336938509107200, 1666841485713921875355107328, 197009962099901410137423740928, 1869585269023799799336621047808, 197010097219995907050675634176,
    1666841485713921875355107328, 113983093514463742189258145792, 2385361757827115190342123520, 4380086059685968602439056621568, 26920511266906014291003965440, 2385361757827115190342123520,
    4380086059685968602439056621568, 2385361757827115190342123520, 2385361757827115190342123520, 98890283160204118319612035072, 2453514950907889910066184192, 26920511266906014291003965440,
    98890283160204118319612035072, 113983093514463742189258145792, 2385361757827115190342123520, 2453514950907889910066184192, 2385361757827115190342123520, 824062168608848829438882742272,
    2971805385489516790452597030912, 824231520778714974624656916480, 6730475381054968371267764224, 134540221096956192138199040, 258848719299861169290082254848, 1518382495237077025559674880,
    134540221096956192138199040, 258848719299861169290082254848, 134540221096956192138199040, 134540221096956192138199040
  ]
def negativeScales : Array ℕ := #[
    48, 31, 32, 37, 32, 31,
    41, 37, 45, 37, 32, 37,
    32, 37, 32, 41, 49, 13,
    56, 17, 13, 54, 13, 13,
    19, 11, 17, 19, 51, 13,
    11, 13, 25, 34, 39, 36,
    25, 34, 13, 39, 17, 13,
    39, 13, 13, 19, 11, 17,
    19, 34, 13, 11, 13, 50,
    52, 48, 29, 13, 34, 17,
    13, 34, 13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48018268636077109, 31658610901036269, 32395576495175996, 37331036242981281, 32395576495175996, 31658610901036269,
    41332803169155469, 37368269149180257, 45675260195853233, 37331036242981281, 32395576495175996, 37368269149180257,
    32395576495175996, 37331036242981281, 32395576495175996, 41412195574642377, 49327648806588087, 13717997652637148,
    56626422062884860, 17214423478646730, 13717997652637148, 54626422341260796, 13717997652637148, 13717997652637148,
    19091546439649009, 11758639637295877, 17214423478646730, 19091546439649009, 51327663647807318, 13717997652637148,
    11758639637295877, 13717997652637148, 25429175474532665, 34314183335266637, 39560561118510096, 36314184324744638,
    25429175474532665, 34524734604969423, 13946266649986186, 39788802063230556, 17442692466319882, 13946266649986186,
    39788802063230556, 13946266649986186, 13946266649986186, 19319815427322126, 11986908643884053, 17442692466319882,
    19319815427322126, 34524734604969423, 13946266649986186, 11986908643884053, 13946266649986186, 50378667932540556,
    52229182487873448, 48378964388855426, 29442766969568483, 13798168001833534, 34708023932046679, 17294593827330713,
    13798168001833534, 34708023932046679, 13798168001833534, 13798168001833534
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
noncomputable def negativeCeiling : ℝ := 4979031559 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 41081751585925707035237670715392, coefficient := (-41081751585925707035237670715392) }, { argument := 125066564558846528819350732800, coefficient := (-125066564558846528819350732800) }, { argument := 6513883570773256709341184000, coefficient := (-6513883570773256709341184000) }, { argument := 199324837265661655305840230400, coefficient := (-199324837265661655305840230400) }, { argument := 208444274264744214698917888000, coefficient := (-208444274264744214698917888000) }, { argument := 125066564558846528819350732800, coefficient := (-125066564558846528819350732800) }, { argument := 3193105726393050438919048396800, coefficient := (-3193105726393050438919048396800) }, { argument := 204535944122280260673313177600, coefficient := (-204535944122280260673313177600) }, { argument := 4048583826928202257443453927424, coefficient := (-4048583826928202257443453927424) }, { argument := 199324837265661655305840230400, coefficient := (-199324837265661655305840230400) }, { argument := 6513883570773256709341184000, coefficient := (-6513883570773256709341184000) }, { argument := 204535944122280260673313177600, coefficient := (-204535944122280260673313177600) }, { argument := 6513883570773256709341184000, coefficient := (-6513883570773256709341184000) }, { argument := 199324837265661655305840230400, coefficient := (-199324837265661655305840230400) }, { argument := 208444274264744214698917888000, coefficient := (-208444274264744214698917888000) }, { argument := 26357415596285174186153869312, coefficient := (-26357415596285174186153869312) }, { argument := 795429492644183174702056865792, coefficient := (-795429492644183174702056865792) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 31310599272741510576493178126336, coefficient := (-31310599272741510576493178126336) }, { argument := 1436307765764802591745638400, coefficient := (-1436307765764802591745638400) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 31310605314294276023900954427392, coefficient := (-31310605314294276023900954427392) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 5276158400315768507906129920, coefficient := (-5276158400315768507906129920) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 1436307765764802591745638400, coefficient := (-1436307765764802591745638400) }, { argument := 5276158400315768507906129920, coefficient := (-5276158400315768507906129920) }, { argument := 795437675388193329551866068992, coefficient := (-795437675388193329551866068992) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 127267776713336938509107200, coefficient := (-127267776713336938509107200) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 197009962099901410137423740928, coefficient := (-197009962099901410137423740928) }, { argument := 1869585269023799799336621047808, coefficient := (-1869585269023799799336621047808) }, { argument := 197010097219995907050675634176, coefficient := (-197010097219995907050675634176) }, { argument := 1666841485713921875355107328, coefficient := (-1666841485713921875355107328) }, { argument := 113983093514463742189258145792, coefficient := (-113983093514463742189258145792) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 4380086059685968602439056621568, coefficient := (-4380086059685968602439056621568) }, { argument := 26920511266906014291003965440, coefficient := (-26920511266906014291003965440) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 4380086059685968602439056621568, coefficient := (-4380086059685968602439056621568) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 98890283160204118319612035072, coefficient := (-98890283160204118319612035072) }, { argument := 2453514950907889910066184192, coefficient := (-2453514950907889910066184192) }, { argument := 26920511266906014291003965440, coefficient := (-26920511266906014291003965440) }, { argument := 98890283160204118319612035072, coefficient := (-98890283160204118319612035072) }, { argument := 113983093514463742189258145792, coefficient := (-113983093514463742189258145792) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 2453514950907889910066184192, coefficient := (-2453514950907889910066184192) }, { argument := 2385361757827115190342123520, coefficient := (-2385361757827115190342123520) }, { argument := 824062168608848829438882742272, coefficient := (-824062168608848829438882742272) }, { argument := 2971805385489516790452597030912, coefficient := (-2971805385489516790452597030912) }, { argument := 824231520778714974624656916480, coefficient := (-824231520778714974624656916480) }, { argument := 6730475381054968371267764224, coefficient := (-6730475381054968371267764224) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 258848719299861169290082254848, coefficient := (-258848719299861169290082254848) }, { argument := 1518382495237077025559674880, coefficient := (-1518382495237077025559674880) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 258848719299861169290082254848, coefficient := (-258848719299861169290082254848) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }, { argument := 134540221096956192138199040, coefficient := (-134540221096956192138199040) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
