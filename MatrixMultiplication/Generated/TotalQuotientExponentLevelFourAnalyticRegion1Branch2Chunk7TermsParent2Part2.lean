import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2055897445958224872139722342793216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    27852979035, 697825065, 17482185, 2040087987, 76651346509, 153291098411,
    4091770581, 1299954377220849, 9975, 3255, 17651137361644641, 32865,
    5199817297487835, 65835, 29505, 9975, 3255, 64970955,
    2441125685, 4881882115, 130311165, 15768687315, 1425, 465,
    27081872685, 4695, 15768687315, 9405, 4215, 1425,
    465, 15890531, 15890531, 84645, 65835, 9405,
    88407, 1043955, 73359, 65835, 1043955, 9405,
    73359, 73359, 73359, 73359, 73359, 84645,
    88407, 4371045, 697825065, 27852979035, 697825065, 17482185,
    37935, 29505, 4215, 39621, 467865, 32877,
    29505, 467865, 4215, 32877
  ]
def negativeCoefficients : Array ℕ := #[
    128449193987260658959924592640, 12872600382274732647556055040, 80622348136061004404490240, 75265961968076597557916073984, 2827935543913506155882073817088, 2827721661165541914598940082176,
    75479844716040838841049808896, 5854474048850460749966138671104, 376844845332997688052940800, 15371302901740695170580480, 19873413911142061275522199977984, 310401148919021779896238080,
    5854473810840218313121899479040, 310896997399723092643676160, 278666846154137764060200960, 376844845332997688052940800, 15371302901740695170580480, 2397005158218999922226626560,
    90061641525907839359301713920, 90054829973424901738819747840, 2403816710701937542708592640, 145440469639077615780778475520, 430679823237711643489075200, 17567203316275080194949120,
    499572374456980332532948008960, 354744170193167748452843520, 145440469639077615780778475520, 355310854171112105878487040, 318476395604728873211658240, 430679823237711643489075200,
    17567203316275080194949120, 37520455494700533113618956288, 37520455494700533113618956288, 399724710942501119113297920, 310896997399723092643676160, 355310854171112105878487040,
    417490253651056724407222272, 4929938101624180469064007680, 11085698650138697703408795648, 310896997399723092643676160, 4929938101624180469064007680, 355310854171112105878487040,
    346428082816834303231524864, 346428082816834303231524864, 346428082816834303231524864, 11085698650138697703408795648, 346428082816834303231524864, 399724710942501119113297920,
    417490253651056724407222272, 80631548449667767043358720, 12872600382274732647556055040, 128449193987260658959924592640, 12872600382274732647556055040, 80622348136061004404490240,
    358285945055319982363115520, 278666846154137764060200960, 318476395604728873211658240, 374209764835556426023698432, 4418859989015613115811758080, 9936463542867540844203737088,
    278666846154137764060200960, 4418859989015613115811758080, 318476395604728873211658240, 310514485714610651381366784
  ]
def negativeScales : Array ℕ := #[
    34, 29, 24, 30, 36, 37,
    31, 50, 13, 11, 53, 15,
    52, 16, 14, 13, 11, 25,
    31, 32, 26, 33, 10, 8,
    34, 12, 33, 13, 12, 10,
    8, 23, 23, 16, 16, 13,
    16, 19, 16, 16, 19, 13,
    16, 16, 16, 16, 16, 16,
    16, 22, 29, 34, 29, 24,
    15, 14, 12, 15, 18, 15,
    14, 18, 12, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34697112589223745, 29378290177355982, 24059382174660044, 30925984236459982, 36157592084329682, 37157482966125103,
    31930078119161626, 50207382415093232, 13284101125997071, 11668441828086828, 53970610680313680, 15004264364598741,
    52207382356441302, 16006567150468162, 14848671839575775, 13284101125997071, 11668441828086828, 25953291586565642,
    31184899430325417, 32184790312120838, 26957385469542887, 33876343517805173, 10476746203939589, 8861086908132560,
    34656608452211647, 12196909442541137, 33876343517805173, 13199212228410558, 12041316915829445, 10476746203939589,
    8861086908132560, 23921664005391931, 23921664005391931, 16369137229852872, 16006567150468162, 13199212228410558,
    16431872985200856, 19993628116142017, 16162686352385444, 16006567150468162, 19993628116142017, 13199212228410558,
    16162686352385444, 16162686352385444, 16162686352385444, 16162686352385444, 16162686352385444, 16369137229852872,
    16431872985200856, 22059546800099931, 29378290177355982, 34697112589223745, 29378290177355982, 24059382174660044,
    15211241917271758, 14848671839575775, 12041316915829445, 15273977672619720, 18835732783495415, 15004791039804331,
    14848671839575775, 18835732783495415, 12041316915829445, 15004791039804331
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
noncomputable def negativeCeiling : ℝ := 11616324703 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 128449193987260658959924592640, coefficient := (-128449193987260658959924592640) }, { argument := 12872600382274732647556055040, coefficient := (-12872600382274732647556055040) }, { argument := 80622348136061004404490240, coefficient := (-80622348136061004404490240) }, { argument := 75265961968076597557916073984, coefficient := (-75265961968076597557916073984) }, { argument := 2827935543913506155882073817088, coefficient := (-2827935543913506155882073817088) }, { argument := 2827721661165541914598940082176, coefficient := (-2827721661165541914598940082176) }, { argument := 75479844716040838841049808896, coefficient := (-75479844716040838841049808896) }, { argument := 5854474048850460749966138671104, coefficient := (-5854474048850460749966138671104) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 19873413911142061275522199977984, coefficient := (-19873413911142061275522199977984) }, { argument := 310401148919021779896238080, coefficient := (-310401148919021779896238080) }, { argument := 5854473810840218313121899479040, coefficient := (-5854473810840218313121899479040) }, { argument := 310896997399723092643676160, coefficient := (-310896997399723092643676160) }, { argument := 278666846154137764060200960, coefficient := (-278666846154137764060200960) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 2397005158218999922226626560, coefficient := (-2397005158218999922226626560) }, { argument := 90061641525907839359301713920, coefficient := (-90061641525907839359301713920) }, { argument := 90054829973424901738819747840, coefficient := (-90054829973424901738819747840) }, { argument := 2403816710701937542708592640, coefficient := (-2403816710701937542708592640) }, { argument := 145440469639077615780778475520, coefficient := (-145440469639077615780778475520) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 499572374456980332532948008960, coefficient := (-499572374456980332532948008960) }, { argument := 354744170193167748452843520, coefficient := (-354744170193167748452843520) }, { argument := 145440469639077615780778475520, coefficient := (-145440469639077615780778475520) }, { argument := 355310854171112105878487040, coefficient := (-355310854171112105878487040) }, { argument := 318476395604728873211658240, coefficient := (-318476395604728873211658240) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 17567203316275080194949120, coefficient := (-17567203316275080194949120) }, { argument := 37520455494700533113618956288, coefficient := (-37520455494700533113618956288) }, { argument := 37520455494700533113618956288, coefficient := (-37520455494700533113618956288) }, { argument := 399724710942501119113297920, coefficient := (-399724710942501119113297920) }, { argument := 310896997399723092643676160, coefficient := (-310896997399723092643676160) }, { argument := 355310854171112105878487040, coefficient := (-355310854171112105878487040) }, { argument := 417490253651056724407222272, coefficient := (-417490253651056724407222272) }, { argument := 4929938101624180469064007680, coefficient := (-4929938101624180469064007680) }, { argument := 11085698650138697703408795648, coefficient := (-11085698650138697703408795648) }, { argument := 310896997399723092643676160, coefficient := (-310896997399723092643676160) }, { argument := 4929938101624180469064007680, coefficient := (-4929938101624180469064007680) }, { argument := 355310854171112105878487040, coefficient := (-355310854171112105878487040) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 11085698650138697703408795648, coefficient := (-11085698650138697703408795648) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 399724710942501119113297920, coefficient := (-399724710942501119113297920) }, { argument := 417490253651056724407222272, coefficient := (-417490253651056724407222272) }, { argument := 80631548449667767043358720, coefficient := (-80631548449667767043358720) }, { argument := 12872600382274732647556055040, coefficient := (-12872600382274732647556055040) }, { argument := 128449193987260658959924592640, coefficient := (-128449193987260658959924592640) }, { argument := 12872600382274732647556055040, coefficient := (-12872600382274732647556055040) }, { argument := 80622348136061004404490240, coefficient := (-80622348136061004404490240) }, { argument := 358285945055319982363115520, coefficient := (-358285945055319982363115520) }, { argument := 278666846154137764060200960, coefficient := (-278666846154137764060200960) }, { argument := 318476395604728873211658240, coefficient := (-318476395604728873211658240) }, { argument := 374209764835556426023698432, coefficient := (-374209764835556426023698432) }, { argument := 4418859989015613115811758080, coefficient := (-4418859989015613115811758080) }, { argument := 9936463542867540844203737088, coefficient := (-9936463542867540844203737088) }, { argument := 278666846154137764060200960, coefficient := (-278666846154137764060200960) }, { argument := 4418859989015613115811758080, coefficient := (-4418859989015613115811758080) }, { argument := 318476395604728873211658240, coefficient := (-318476395604728873211658240) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1614947286870585545678121785622528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    32877, 32877, 32877, 32877, 37935, 39621,
    147925365, 23615869305, 942603448395, 23615869305, 591633945, 1988111223,
    74698445961, 149385592719, 3987521649, 8051925, 1285467225, 51308119275,
    1285467225, 32204025, 1130494617, 42475586919, 84944748801, 2267414271,
    13967102607, 13395, 4371, 23992462449, 44133, 13967102607,
    88407, 39621, 13395, 4371, 12825, 9975,
    1425, 13395, 158175, 11115, 9975, 158175,
    1425, 11115, 11115, 11115, 11115, 11115,
    12825, 13395, 267553965, 42714239505, 1704895506195, 42714239505,
    1070093745, 2040087987, 76651346509, 153291098411, 4091770581, 147925365,
    23615869305, 942603448395, 23615869305, 591633945
  ]
def negativeCoefficients : Array ℕ := #[
    310514485714610651381366784, 310514485714610651381366784, 9936463542867540844203737088, 310514485714610651381366784, 358285945055319982363115520, 374209764835556426023698432,
    1364370675082536163391569920, 217817948573754028746803773440, 2173495571942331676611355607040, 217817948573754028746803773440, 1364214996091769100844400640, 73348357841501397620134772736,
    2755886230692779884394632445952, 2755677797186801993207884283904, 73556791347479288806882934784, 74265899887851890697830400, 11856342457358306385906892800, 118308468146161133252562124800,
    11856342457358306385906892800, 74257425914793030372556800, 41707889753010598646743302144, 1567072562550796404851849822208, 1566954041537593290255463612416, 41826410766213713243129511936,
    128823783621285239268317331456, 506048792304311181099663360, 20641463896623219229065216, 442582814494789705279507267584, 416824399976972104432091136, 128823783621285239268317331456,
    417490253651056724407222272, 374209764835556426023698432, 506048792304311181099663360, 20641463896623219229065216, 484514801142425598925209600, 376844845332997688052940800,
    430679823237711643489075200, 506048792304311181099663360, 5975682547423249053410918400, 13437210485016603276859146240, 376844845332997688052940800, 5975682547423249053410918400,
    430679823237711643489075200, 419912827656768852401848320, 419912827656768852401848320, 419912827656768852401848320, 13437210485016603276859146240, 419912827656768852401848320,
    484514801142425598925209600, 506048792304311181099663360, 2467749759130621396616478720, 393969322225934580765991895040, 3931221384399582799220850032640, 393969322225934580765991895040,
    2467468181111551266379530240, 75265961968076597557916073984, 2827935543913506155882073817088, 2827721661165541914598940082176, 75479844716040838841049808896, 1364370675082536163391569920,
    217817948573754028746803773440, 2173495571942331676611355607040, 217817948573754028746803773440, 1364214996091769100844400640
  ]
def negativeScales : Array ℕ := #[
    15, 15, 15, 15, 15, 15,
    27, 34, 39, 34, 29, 30,
    36, 37, 31, 22, 30, 35,
    30, 24, 30, 35, 36, 31,
    33, 13, 12, 34, 15, 33,
    16, 15, 13, 12, 13, 13,
    10, 13, 17, 13, 13, 17,
    10, 13, 13, 13, 13, 13,
    13, 13, 27, 35, 40, 35,
    29, 30, 36, 37, 31, 27,
    34, 39, 34, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15004791039804331, 15004791039804331, 15004791039804331, 15004791039804331, 15211241917271758, 15273977672619720,
    27140294213984293, 34459037591240406, 39777860003449025, 34459037591240406, 29140129588544405, 30888751326917220,
    36120359178130707, 37120250059926127, 31892845209385586, 22940902312533566, 30259645680857361, 35578468092660583,
    30259645680857361, 24940737687068613, 30074306976508349, 35305914831286783, 36305805713082204, 31078400858702016,
    33701313722161910, 13709406960819918, 12093747662785669, 34481862184064398, 15429570199331434, 33701313722161910,
    16431872985200856, 15273977672619720, 13709406960819918, 12093747662785669, 13646671205401350, 13284101125997071,
    10476746203939589, 13709406960819918, 17271162070289573, 13440220327914385, 13284101125997071, 17271162070289573,
    10476746203939589, 13440220327914385, 13440220327914385, 13440220327914385, 13440220327914385, 13440220327914385,
    13646671205401350, 13709406960819918, 27995254690076254, 35313998045385613, 40632820457199430, 35313998045385613,
    29995090064578523, 30925984236459982, 36157592084329682, 37157482966125103, 31930078119161626, 27140294213984293,
    34459037591240406, 39777860003449025, 34459037591240406, 29140129588544405
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
noncomputable def negativeCeiling : ℝ := 11480848413 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 9936463542867540844203737088, coefficient := (-9936463542867540844203737088) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 358285945055319982363115520, coefficient := (-358285945055319982363115520) }, { argument := 374209764835556426023698432, coefficient := (-374209764835556426023698432) }, { argument := 1364370675082536163391569920, coefficient := (-1364370675082536163391569920) }, { argument := 217817948573754028746803773440, coefficient := (-217817948573754028746803773440) }, { argument := 2173495571942331676611355607040, coefficient := (-2173495571942331676611355607040) }, { argument := 217817948573754028746803773440, coefficient := (-217817948573754028746803773440) }, { argument := 1364214996091769100844400640, coefficient := (-1364214996091769100844400640) }, { argument := 73348357841501397620134772736, coefficient := (-73348357841501397620134772736) }, { argument := 2755886230692779884394632445952, coefficient := (-2755886230692779884394632445952) }, { argument := 2755677797186801993207884283904, coefficient := (-2755677797186801993207884283904) }, { argument := 73556791347479288806882934784, coefficient := (-73556791347479288806882934784) }, { argument := 74265899887851890697830400, coefficient := (-74265899887851890697830400) }, { argument := 11856342457358306385906892800, coefficient := (-11856342457358306385906892800) }, { argument := 118308468146161133252562124800, coefficient := (-118308468146161133252562124800) }, { argument := 11856342457358306385906892800, coefficient := (-11856342457358306385906892800) }, { argument := 74257425914793030372556800, coefficient := (-74257425914793030372556800) }, { argument := 41707889753010598646743302144, coefficient := (-41707889753010598646743302144) }, { argument := 1567072562550796404851849822208, coefficient := (-1567072562550796404851849822208) }, { argument := 1566954041537593290255463612416, coefficient := (-1566954041537593290255463612416) }, { argument := 41826410766213713243129511936, coefficient := (-41826410766213713243129511936) }, { argument := 128823783621285239268317331456, coefficient := (-128823783621285239268317331456) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 442582814494789705279507267584, coefficient := (-442582814494789705279507267584) }, { argument := 416824399976972104432091136, coefficient := (-416824399976972104432091136) }, { argument := 128823783621285239268317331456, coefficient := (-128823783621285239268317331456) }, { argument := 417490253651056724407222272, coefficient := (-417490253651056724407222272) }, { argument := 374209764835556426023698432, coefficient := (-374209764835556426023698432) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 376844845332997688052940800, coefficient := (-376844845332997688052940800) }, { argument := 5975682547423249053410918400, coefficient := (-5975682547423249053410918400) }, { argument := 430679823237711643489075200, coefficient := (-430679823237711643489075200) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 2467749759130621396616478720, coefficient := (-2467749759130621396616478720) }, { argument := 393969322225934580765991895040, coefficient := (-393969322225934580765991895040) }, { argument := 3931221384399582799220850032640, coefficient := (-3931221384399582799220850032640) }, { argument := 393969322225934580765991895040, coefficient := (-393969322225934580765991895040) }, { argument := 2467468181111551266379530240, coefficient := (-2467468181111551266379530240) }, { argument := 75265961968076597557916073984, coefficient := (-75265961968076597557916073984) }, { argument := 2827935543913506155882073817088, coefficient := (-2827935543913506155882073817088) }, { argument := 2827721661165541914598940082176, coefficient := (-2827721661165541914598940082176) }, { argument := 75479844716040838841049808896, coefficient := (-75479844716040838841049808896) }, { argument := 1364370675082536163391569920, coefficient := (-1364370675082536163391569920) }, { argument := 217817948573754028746803773440, coefficient := (-217817948573754028746803773440) }, { argument := 2173495571942331676611355607040, coefficient := (-2173495571942331676611355607040) }, { argument := 217817948573754028746803773440, coefficient := (-217817948573754028746803773440) }, { argument := 1364214996091769100844400640, coefficient := (-1364214996091769100844400640) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
