import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6380259964981439351584553374318592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    75, 1503, 2523, 2421, 75, 2421,
    1617, 39, 1503, 9, 30039186527445, 515977308875563,
    2881285, 20427823, 954467883, 8154855, 257988732817889, 954467883,
    2881285, 23049255, 19762215, 23049255, 8154855, 19762215,
    15019514883615, 20427823, 81598540044935, 5342400809402921, 16950304665, 44863198238747859,
    17393449885, 553931525, 16950304665, 9638408535, 17393449885, 271537233555,
    332358915, 2671201745934331, 16950304665, 553931525, 332358915, 553931525,
    8530545485, 9638408535, 81598539187847, 22905, 17815, 2545,
    23923, 282495, 19851, 17815, 282495, 2545,
    19851, 19851, 19851, 19851, 19851, 22905,
    23923, 5619915, 897203655, 35810973045
  ]
def negativeCoefficients : Array ℕ := #[
    1450710983537555009647411200, 29072248110092602393334120448, 48801917486203350524538912768, 46828950548592275711418433536, 1450710983537555009647411200, 46828950548592275711418433536,
    31277328805069686007998185472, 1508739422879057210033307648, 29072248110092602393334120448, 1392682544196052809261514752, 135284469251514125714687262720, 2323755215983616845244161589248,
    108851869692760525676352634880, 96467666653193644498179063808, 4507347139654746032077503725568, 1232326845589182099812316610560, 2323755921968862705762999205888, 4507347139654746032077503725568,
    108851869692760525676352634880, 108847029267115584290008596480, 93324421743263745686781296640, 108847029267115584290008596480, 1232326845589182099812316610560, 93324421743263745686781296640,
    135283763266268265195849646080, 96467666653193644498179063808, 91871788635086440482933309440, 6015008573622707809647752904704, 1250711728506640466446972354560, 50511470717668387558527929942016,
    1283410074349951328314867056640, 40872932304138577334868377600, 1250711728506640466446972354560, 711189022092011245626709770240, 1283410074349951328314867056640, 20035911415488730609552478699520,
    784760300239460684829472849920, 6015011593810635710078111449088, 1250711728506640466446972354560, 40872932304138577334868377600, 784760300239460684829472849920, 40872932304138577334868377600,
    1258886314967468181913946030080, 711189022092011245626709770240, 91871787670091141127002390528, 216331608580258447239413760, 168257917784645458963988480, 192294763182451953101701120,
    225946346739381044894498816, 2668089839156520849286103040, 5999596611292500936773074944, 168257917784645458963988480, 2668089839156520849286103040, 192294763182451953101701120,
    187487394102890654274158592, 187487394102890654274158592, 187487394102890654274158592, 5999596611292500936773074944, 187487394102890654274158592, 216331608580258447239413760,
    225946346739381044894498816, 207338267442002829540065280, 33100972411563598236572712960, 330297927395813123039806095360
  ]
def negativeScales : Array ℕ := #[
    6, 10, 11, 11, 6, 11,
    10, 5, 10, 3, 44, 48,
    21, 24, 29, 22, 47, 29,
    21, 24, 24, 24, 22, 24,
    43, 24, 46, 52, 33, 55,
    34, 29, 33, 33, 34, 37,
    28, 51, 33, 29, 28, 29,
    32, 33, 46, 14, 14, 11,
    14, 18, 14, 14, 18, 11,
    14, 14, 14, 14, 14, 14,
    14, 22, 29, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    6228818690495881, 10553629293917849, 11300924490976301, 11241387363998937, 6228818690495881, 11241387363998937,
    10659103963500476, 5285402218862249, 10553629293917849, 3169925001442313, 44771910978548789, 48874300952828774,
    21458280939905604, 24284032127976593, 29830121413312221, 22959227806361640, 47874301391137122, 29830121413312221,
    21458280939905604, 24458216784706765, 24236241321175881, 24458216784706765, 22959227806361640, 24236241321175881,
    43771903449790431, 24284032127976593, 46213608573370047, 52246409640400302, 33980592170803813, 55316381990131373,
    34017825059686990, 29045132405682725, 33980592170803813, 33166147806644091, 34017825059686990, 37982359097483404,
    28308166811516519, 51246410364789802, 33980592170803813, 29045132405682725, 28308166811516519, 29045132405682725,
    32989990871656069, 33166147806644091, 46213608558216386, 14483374942405524, 14120804863020662, 11313449940963058,
    14546110697754515, 18107865807313164, 14276924064937944, 14120804863020662, 18107865807313164, 11313449940963058,
    14276924064937944, 14276924064937944, 14276924064937944, 14276924064937944, 14276924064937944, 14483374942405524,
    14546110697754515, 22422116879484655, 29740860256924610, 35059682668540829
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
noncomputable def negativeCeiling : ℝ := 6180538587 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 31277328805069686007998185472, coefficient := (-31277328805069686007998185472) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 135284469251514125714687262720, coefficient := (-135284469251514125714687262720) }, { argument := 2323755215983616845244161589248, coefficient := (-2323755215983616845244161589248) }, { argument := 108851869692760525676352634880, coefficient := (-108851869692760525676352634880) }, { argument := 96467666653193644498179063808, coefficient := (-96467666653193644498179063808) }, { argument := 4507347139654746032077503725568, coefficient := (-4507347139654746032077503725568) }, { argument := 1232326845589182099812316610560, coefficient := (-1232326845589182099812316610560) }, { argument := 2323755921968862705762999205888, coefficient := (-2323755921968862705762999205888) }, { argument := 4507347139654746032077503725568, coefficient := (-4507347139654746032077503725568) }, { argument := 108851869692760525676352634880, coefficient := (-108851869692760525676352634880) }, { argument := 108847029267115584290008596480, coefficient := (-108847029267115584290008596480) }, { argument := 93324421743263745686781296640, coefficient := (-93324421743263745686781296640) }, { argument := 108847029267115584290008596480, coefficient := (-108847029267115584290008596480) }, { argument := 1232326845589182099812316610560, coefficient := (-1232326845589182099812316610560) }, { argument := 93324421743263745686781296640, coefficient := (-93324421743263745686781296640) }, { argument := 135283763266268265195849646080, coefficient := (-135283763266268265195849646080) }, { argument := 96467666653193644498179063808, coefficient := (-96467666653193644498179063808) }, { argument := 91871788635086440482933309440, coefficient := (-91871788635086440482933309440) }, { argument := 6015008573622707809647752904704, coefficient := (-6015008573622707809647752904704) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 50511470717668387558527929942016, coefficient := (-50511470717668387558527929942016) }, { argument := 1283410074349951328314867056640, coefficient := (-1283410074349951328314867056640) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 711189022092011245626709770240, coefficient := (-711189022092011245626709770240) }, { argument := 1283410074349951328314867056640, coefficient := (-1283410074349951328314867056640) }, { argument := 20035911415488730609552478699520, coefficient := (-20035911415488730609552478699520) }, { argument := 784760300239460684829472849920, coefficient := (-784760300239460684829472849920) }, { argument := 6015011593810635710078111449088, coefficient := (-6015011593810635710078111449088) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 784760300239460684829472849920, coefficient := (-784760300239460684829472849920) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 1258886314967468181913946030080, coefficient := (-1258886314967468181913946030080) }, { argument := 711189022092011245626709770240, coefficient := (-711189022092011245626709770240) }, { argument := 91871787670091141127002390528, coefficient := (-91871787670091141127002390528) }, { argument := 216331608580258447239413760, coefficient := (-216331608580258447239413760) }, { argument := 168257917784645458963988480, coefficient := (-168257917784645458963988480) }, { argument := 192294763182451953101701120, coefficient := (-192294763182451953101701120) }, { argument := 225946346739381044894498816, coefficient := (-225946346739381044894498816) }, { argument := 2668089839156520849286103040, coefficient := (-2668089839156520849286103040) }, { argument := 5999596611292500936773074944, coefficient := (-5999596611292500936773074944) }, { argument := 168257917784645458963988480, coefficient := (-168257917784645458963988480) }, { argument := 2668089839156520849286103040, coefficient := (-2668089839156520849286103040) }, { argument := 192294763182451953101701120, coefficient := (-192294763182451953101701120) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 5999596611292500936773074944, coefficient := (-5999596611292500936773074944) }, { argument := 187487394102890654274158592, coefficient := (-187487394102890654274158592) }, { argument := 216331608580258447239413760, coefficient := (-216331608580258447239413760) }, { argument := 225946346739381044894498816, coefficient := (-225946346739381044894498816) }, { argument := 207338267442002829540065280, coefficient := (-207338267442002829540065280) }, { argument := 33100972411563598236572712960, coefficient := (-33100972411563598236572712960) }, { argument := 330297927395813123039806095360, coefficient := (-330297927395813123039806095360) }] }

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
def constantNumerator : ℤ := (-17701599492840098562229394990956544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    897203655, 22477095, 10773314095243, 1535761143, 2964317549470919, 38001919347,
    1209003453, 23714476485432361, 620839611, 620839611, 21010519467, 1143651915,
    38001919347, 21010519467, 689558746587871, 1209003453, 1143651915, 1535761143,
    1833867, 292771719, 11685685941, 292771719, 7334631, 774268929,
    29091272703, 58178144937, 1552938327, 81360499379913, 2705885, 882973,
    69477802703113, 8915179, 81360497945875, 17858841, 8003723, 2705885,
    882973, 30038999509803, 515961582703829, 2881285, 20427823, 954467883,
    8154855, 257980869733919, 954467883, 2881285, 23049255, 19762215,
    23049255, 8154855, 19762215, 15019421372897, 20427823, 557469918934577,
    18199387200291085, 29093716071, 152483757575331663, 29854336099, 950775035, 29093716071,
    16543485609, 29854336099, 466069922157, 570465021
  ]
def negativeCoefficients : Array ℕ := #[
    33100972411563598236572712960, 207314609492728297040117760, 194074773379526748213568602112, 7082448190817164309951414272, 6675049705602526325277995302912, 175252920125965150903691378688,
    5575544320430533605706432512, 6675031716442473163329755938816, 5726234707469196676130930688, 5726234707469196676130930688, 96893918865860354282952327168, 5274163546353207464857436160,
    175252920125965150903691378688, 96893918865860354282952327168, 194093532136450132231246053376, 5575544320430533605706432512, 5274163546353207464857436160, 7082448190817164309951414272,
    8457218803555378573344768, 1350171243103252033333886976, 13472678617460798439781564416, 1350171243103252033333886976, 8456253808256022642425856, 7141370388744095793395269632,
    268319631165366849438455169024, 268299337584005026289232642048, 7161663970105918942617796608, 91603778672513414417677811712, 199659072351558280297840640, 8143988477497771959517184,
    312900206364260546529143554048, 164456025384309846666379264, 91603777057930163808894976000, 164718734690035581245718528, 147642629817862833588666368, 199659072351558280297840640,
    8143988477497771959517184, 135283626998931302805864972288, 2323684391602455638417220829184, 108851869692760525676352634880, 96467666653193644498179063808, 4507347139654746032077503725568,
    1232326845589182099812316610560, 2323685097604788155922302107648, 4507347139654746032077503725568, 108851869692760525676352634880, 108847029267115584290008596480, 93324421743263745686781296640,
    108847029267115584290008596480, 1232326845589182099812316610560, 93324421743263745686781296640, 135282920996598785300783693824, 96467666653193644498179063808, 313827664898002698711045505024,
    20490688353400576214396085207040, 4293474676119260723492985765888, 171681448449079181033679945203712, 4405722380070091069205220687872, 140309629938537932140293652480, 4293474676119260723492985765888,
    2441387560930560019241109553152, 4405722380070091069205220687872, 68779780595871294335171948445696, 2693944894819928297093638127616
  ]
def negativeScales : Array ℕ := #[
    29, 24, 43, 30, 51, 35,
    30, 54, 29, 29, 34, 30,
    35, 34, 49, 30, 30, 30,
    20, 28, 33, 28, 22, 29,
    34, 35, 30, 46, 21, 19,
    45, 23, 46, 24, 22, 21,
    19, 44, 48, 21, 24, 29,
    22, 47, 29, 21, 24, 24,
    24, 22, 24, 43, 24, 48,
    54, 34, 57, 34, 29, 34,
    33, 34, 38, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29740860256924610, 24421952254044768, 43292527354661475, 30516306705068158, 51396621426456166, 35145353234863276,
    30171171219019007, 54396617538409168, 29209645366833643, 29209645366833643, 34290392780718005, 30091000870335024,
    35145353234863276, 34290392780718005, 49292666795029084, 30171171219019007, 30091000870335024, 30516306705068158,
    20806457582277085, 28125200958796615, 33444023370596794, 28125200958796615, 22806292956834750, 29528259507830139,
    34759867362886475, 35759758244681241, 30532353390023899, 46209393767828383, 21367669095462265, 19752009797753153,
    45981617379407746, 23087832334063933, 46209393742399833, 24090135119933354, 22932239815051004, 21367669095462265,
    19752009797753153, 44771901996605607, 48874256981094967, 21458280939905604, 24284032127976593, 29830121413312221,
    22959227806361640, 47874257419427283, 29830121413312221, 21458280939905604, 24458216784706765, 24236241321175881,
    24458216784706765, 22959227806361640, 24236241321175881, 43771894467618160, 24284032127976593, 48985887306633066,
    54014739391809400, 34759988529358935, 57081433189442652, 34797221435888990, 29824528782330926, 34759988529358935,
    33945544191902317, 34797221435888990, 38761755455543947, 29087563187108130
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
noncomputable def negativeCeiling : ℝ := 23665310431 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33100972411563598236572712960, coefficient := (-33100972411563598236572712960) }, { argument := 207314609492728297040117760, coefficient := (-207314609492728297040117760) }, { argument := 194074773379526748213568602112, coefficient := (-194074773379526748213568602112) }, { argument := 7082448190817164309951414272, coefficient := (-7082448190817164309951414272) }, { argument := 6675049705602526325277995302912, coefficient := (-6675049705602526325277995302912) }, { argument := 175252920125965150903691378688, coefficient := (-175252920125965150903691378688) }, { argument := 5575544320430533605706432512, coefficient := (-5575544320430533605706432512) }, { argument := 6675031716442473163329755938816, coefficient := (-6675031716442473163329755938816) }, { argument := 5726234707469196676130930688, coefficient := (-5726234707469196676130930688) }, { argument := 5726234707469196676130930688, coefficient := (-5726234707469196676130930688) }, { argument := 96893918865860354282952327168, coefficient := (-96893918865860354282952327168) }, { argument := 5274163546353207464857436160, coefficient := (-5274163546353207464857436160) }, { argument := 175252920125965150903691378688, coefficient := (-175252920125965150903691378688) }, { argument := 96893918865860354282952327168, coefficient := (-96893918865860354282952327168) }, { argument := 194093532136450132231246053376, coefficient := (-194093532136450132231246053376) }, { argument := 5575544320430533605706432512, coefficient := (-5575544320430533605706432512) }, { argument := 5274163546353207464857436160, coefficient := (-5274163546353207464857436160) }, { argument := 7082448190817164309951414272, coefficient := (-7082448190817164309951414272) }, { argument := 8457218803555378573344768, coefficient := (-8457218803555378573344768) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 13472678617460798439781564416, coefficient := (-13472678617460798439781564416) }, { argument := 1350171243103252033333886976, coefficient := (-1350171243103252033333886976) }, { argument := 8456253808256022642425856, coefficient := (-8456253808256022642425856) }, { argument := 7141370388744095793395269632, coefficient := (-7141370388744095793395269632) }, { argument := 268319631165366849438455169024, coefficient := (-268319631165366849438455169024) }, { argument := 268299337584005026289232642048, coefficient := (-268299337584005026289232642048) }, { argument := 7161663970105918942617796608, coefficient := (-7161663970105918942617796608) }, { argument := 91603778672513414417677811712, coefficient := (-91603778672513414417677811712) }, { argument := 199659072351558280297840640, coefficient := (-199659072351558280297840640) }, { argument := 8143988477497771959517184, coefficient := (-8143988477497771959517184) }, { argument := 312900206364260546529143554048, coefficient := (-312900206364260546529143554048) }, { argument := 164456025384309846666379264, coefficient := (-164456025384309846666379264) }, { argument := 91603777057930163808894976000, coefficient := (-91603777057930163808894976000) }, { argument := 164718734690035581245718528, coefficient := (-164718734690035581245718528) }, { argument := 147642629817862833588666368, coefficient := (-147642629817862833588666368) }, { argument := 199659072351558280297840640, coefficient := (-199659072351558280297840640) }, { argument := 8143988477497771959517184, coefficient := (-8143988477497771959517184) }, { argument := 135283626998931302805864972288, coefficient := (-135283626998931302805864972288) }, { argument := 2323684391602455638417220829184, coefficient := (-2323684391602455638417220829184) }, { argument := 108851869692760525676352634880, coefficient := (-108851869692760525676352634880) }, { argument := 96467666653193644498179063808, coefficient := (-96467666653193644498179063808) }, { argument := 4507347139654746032077503725568, coefficient := (-4507347139654746032077503725568) }, { argument := 1232326845589182099812316610560, coefficient := (-1232326845589182099812316610560) }, { argument := 2323685097604788155922302107648, coefficient := (-2323685097604788155922302107648) }, { argument := 4507347139654746032077503725568, coefficient := (-4507347139654746032077503725568) }, { argument := 108851869692760525676352634880, coefficient := (-108851869692760525676352634880) }, { argument := 108847029267115584290008596480, coefficient := (-108847029267115584290008596480) }, { argument := 93324421743263745686781296640, coefficient := (-93324421743263745686781296640) }, { argument := 108847029267115584290008596480, coefficient := (-108847029267115584290008596480) }, { argument := 1232326845589182099812316610560, coefficient := (-1232326845589182099812316610560) }, { argument := 93324421743263745686781296640, coefficient := (-93324421743263745686781296640) }, { argument := 135282920996598785300783693824, coefficient := (-135282920996598785300783693824) }, { argument := 96467666653193644498179063808, coefficient := (-96467666653193644498179063808) }, { argument := 313827664898002698711045505024, coefficient := (-313827664898002698711045505024) }, { argument := 20490688353400576214396085207040, coefficient := (-20490688353400576214396085207040) }, { argument := 4293474676119260723492985765888, coefficient := (-4293474676119260723492985765888) }, { argument := 171681448449079181033679945203712, coefficient := (-171681448449079181033679945203712) }, { argument := 4405722380070091069205220687872, coefficient := (-4405722380070091069205220687872) }, { argument := 140309629938537932140293652480, coefficient := (-140309629938537932140293652480) }, { argument := 4293474676119260723492985765888, coefficient := (-4293474676119260723492985765888) }, { argument := 2441387560930560019241109553152, coefficient := (-2441387560930560019241109553152) }, { argument := 4405722380070091069205220687872, coefficient := (-4405722380070091069205220687872) }, { argument := 68779780595871294335171948445696, coefficient := (-68779780595871294335171948445696) }, { argument := 2693944894819928297093638127616, coefficient := (-2693944894819928297093638127616) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
