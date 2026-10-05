import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-1823139802983778787187212414877696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    40747548219, 4547097051, 103803, 546795, 1644357, 54045,
    72063, 119865, 1644357, 1397253, 72063, 22399869,
    709587, 546795, 1644357, 119865, 709587, 119865,
    1648101, 1397253, 57789, 1970253, 10867845, 30129957,
    989445, 11287929, 2162715, 30129957, 24348753, 11287929,
    421128369, 12476637, 10867845, 30129957, 2162715, 12476637,
    2162715, 30217551, 24348753, 1077039, 123520859883, 2251633042425,
    1125816439407, 123521445735, 7515, 22275, 432315, 14175,
    361935, 15075, 432315, 316485, 361935, 6322905,
    20655, 22275, 432315, 15075, 20655, 15075,
    217035, 316485, 7965, 5824026477
  ]
def negativeCoefficients : Array ℕ := #[
    187914898406758111168457342976, 5242445973632276798977867776, 980391616042635564234571776, 20657331048005661236983234560, 31061025530688324778630053888, 1020881186266759902296801280,
    21779705334722255554212790272, 1132092916938340047079342080, 31061025530688324778630053888, 26393362941156241535089508352, 21779705334722255554212790272, 423121562345083187453069623296,
    26807438923840183506007228416, 20657331048005661236983234560, 31061025530688324778630053888, 1132092916938340047079342080, 26807438923840183506007228416, 1132092916938340047079342080,
    31131747691135780585350365184, 26393362941156241535089508352, 1091603346714215709017112576, 18608513459946734182440370176, 410575575752179675099520040960, 569138796268414587575665164288,
    18690087618571824433861754880, 426445900564898171419122204672, 20426265655998849496677089280, 569138796268414587575665164288, 459934940267486890023664484352, 426445900564898171419122204672,
    7954889979004640513809811767296, 471354019101850253200579362816, 410575575752179675099520040960, 569138796268414587575665164288, 20426265655998849496677089280, 471354019101850253200579362816,
    20426265655998849496677089280, 570793400147216522387059113984, 459934940267486890023664484352, 20344691497373759245255704576, 142409855626639884324918263808, 5191912310190247020114581913600,
    5191911932928966439652900732928, 142410531068009201255432847360, 1135634691800492280989614080, 26928822631915864866580070400, 32664797856668650728943779840, 1071032718314835534466252800,
    27347035407638800646704988160, 1139034795668158425543475200, 32664797856668650728943779840, 23912930501295994647305256960, 27347035407638800646704988160, 477745194341902305118472110080,
    24970362804140165603556065280, 26928822631915864866580070400, 32664797856668650728943779840, 1139034795668158425543475200, 24970362804140165603556065280, 1139034795668158425543475200,
    32797401907507630366544363520, 23912930501295994647305256960, 1203636769153815172066836480, 107434325899727268219382136832
  ]
def negativeScales : Array ℕ := #[
    35, 32, 16, 19, 20, 15,
    16, 16, 20, 20, 16, 24,
    19, 19, 20, 16, 19, 16,
    20, 20, 15, 20, 23, 24,
    19, 23, 21, 24, 24, 23,
    28, 23, 23, 24, 21, 23,
    21, 24, 24, 20, 36, 41,
    40, 36, 12, 14, 18, 13,
    18, 13, 18, 18, 18, 22,
    14, 14, 18, 13, 14, 13,
    17, 18, 12, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35245994203831970, 32082298650569747, 16663488613948452, 19060640525156599, 20649092120320883, 15721873532155397,
    16136971092305436, 16871050937283783, 20649092120320883, 20414161841895461, 16136971092305436, 24416986959280010,
    19436620053400322, 19060640525156599, 20649092120320883, 16871050937283783, 19436620053400322, 16871050937283783,
    20652373226755207, 20414161841895461, 15818507285743830, 20909949472448818, 23373562558943139, 24844695279766409,
    19916259995085351, 23428277482873294, 21044412130520006, 24844695279766409, 24537344552052568, 23428277482873294,
    28649684823981229, 23572725781327144, 23373562558943139, 24844695279766409, 21044412130520006, 23572725781327144,
    21044412130520006, 24848883407041059, 24537344552052568, 20038639060699231, 36845963746352264, 41034108863486040,
    40034108758655109, 36845970588951948, 12875557391602924, 14443137811296683, 18721723368736596, 13791061115254762,
    18465371101033474, 13879870384705585, 18721723368736596, 18271777598297583, 18465371101033474, 22592156112886414,
    14334203439743484, 14443137811296683, 18721723368736596, 13879870384705585, 14334203439743484, 13879870384705585,
    17727568191228207, 18271777598297583, 12959458658631210, 32439369768271146
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
noncomputable def negativeCeiling : ℝ := 127276999 / 12500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 187914898406758111168457342976, coefficient := (-187914898406758111168457342976) }, { argument := 5242445973632276798977867776, coefficient := (-5242445973632276798977867776) }, { argument := 980391616042635564234571776, coefficient := (-980391616042635564234571776) }, { argument := 20657331048005661236983234560, coefficient := (-20657331048005661236983234560) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 1020881186266759902296801280, coefficient := (-1020881186266759902296801280) }, { argument := 21779705334722255554212790272, coefficient := (-21779705334722255554212790272) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 26393362941156241535089508352, coefficient := (-26393362941156241535089508352) }, { argument := 21779705334722255554212790272, coefficient := (-21779705334722255554212790272) }, { argument := 423121562345083187453069623296, coefficient := (-423121562345083187453069623296) }, { argument := 26807438923840183506007228416, coefficient := (-26807438923840183506007228416) }, { argument := 20657331048005661236983234560, coefficient := (-20657331048005661236983234560) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 26807438923840183506007228416, coefficient := (-26807438923840183506007228416) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 31131747691135780585350365184, coefficient := (-31131747691135780585350365184) }, { argument := 26393362941156241535089508352, coefficient := (-26393362941156241535089508352) }, { argument := 1091603346714215709017112576, coefficient := (-1091603346714215709017112576) }, { argument := 18608513459946734182440370176, coefficient := (-18608513459946734182440370176) }, { argument := 410575575752179675099520040960, coefficient := (-410575575752179675099520040960) }, { argument := 569138796268414587575665164288, coefficient := (-569138796268414587575665164288) }, { argument := 18690087618571824433861754880, coefficient := (-18690087618571824433861754880) }, { argument := 426445900564898171419122204672, coefficient := (-426445900564898171419122204672) }, { argument := 20426265655998849496677089280, coefficient := (-20426265655998849496677089280) }, { argument := 569138796268414587575665164288, coefficient := (-569138796268414587575665164288) }, { argument := 459934940267486890023664484352, coefficient := (-459934940267486890023664484352) }, { argument := 426445900564898171419122204672, coefficient := (-426445900564898171419122204672) }, { argument := 7954889979004640513809811767296, coefficient := (-7954889979004640513809811767296) }, { argument := 471354019101850253200579362816, coefficient := (-471354019101850253200579362816) }, { argument := 410575575752179675099520040960, coefficient := (-410575575752179675099520040960) }, { argument := 569138796268414587575665164288, coefficient := (-569138796268414587575665164288) }, { argument := 20426265655998849496677089280, coefficient := (-20426265655998849496677089280) }, { argument := 471354019101850253200579362816, coefficient := (-471354019101850253200579362816) }, { argument := 20426265655998849496677089280, coefficient := (-20426265655998849496677089280) }, { argument := 570793400147216522387059113984, coefficient := (-570793400147216522387059113984) }, { argument := 459934940267486890023664484352, coefficient := (-459934940267486890023664484352) }, { argument := 20344691497373759245255704576, coefficient := (-20344691497373759245255704576) }, { argument := 142409855626639884324918263808, coefficient := (-142409855626639884324918263808) }, { argument := 5191912310190247020114581913600, coefficient := (-5191912310190247020114581913600) }, { argument := 5191911932928966439652900732928, coefficient := (-5191911932928966439652900732928) }, { argument := 142410531068009201255432847360, coefficient := (-142410531068009201255432847360) }, { argument := 1135634691800492280989614080, coefficient := (-1135634691800492280989614080) }, { argument := 26928822631915864866580070400, coefficient := (-26928822631915864866580070400) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 1071032718314835534466252800, coefficient := (-1071032718314835534466252800) }, { argument := 27347035407638800646704988160, coefficient := (-27347035407638800646704988160) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 23912930501295994647305256960, coefficient := (-23912930501295994647305256960) }, { argument := 27347035407638800646704988160, coefficient := (-27347035407638800646704988160) }, { argument := 477745194341902305118472110080, coefficient := (-477745194341902305118472110080) }, { argument := 24970362804140165603556065280, coefficient := (-24970362804140165603556065280) }, { argument := 26928822631915864866580070400, coefficient := (-26928822631915864866580070400) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 24970362804140165603556065280, coefficient := (-24970362804140165603556065280) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 32797401907507630366544363520, coefficient := (-32797401907507630366544363520) }, { argument := 23912930501295994647305256960, coefficient := (-23912930501295994647305256960) }, { argument := 1203636769153815172066836480, coefficient := (-1203636769153815172066836480) }, { argument := 107434325899727268219382136832, coefficient := (-107434325899727268219382136832) }] }

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
def constantNumerator : ℤ := (-9539338414141190033170525134520320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    206894801301, 1655158877031, 46592035977, 165449840157, 289455983075, 165449840157,
    9577321771179, 599853367444309, 2254178265, 1161417291, 31171358895, 47900738073,
    37490839181157, 31171358895, 2254178265, 1112990757, 2065080339, 1112990757,
    47900738073, 2065080339, 598578894811, 1161417291, 34270703989271, 4600805174943259,
    398307, 1490096188134463, 272583, 14595, 398307, 344253,
    272583, 5376369, 21789, 2300402992699869, 398307, 14595,
    21789, 14595, 199563, 344253, 8592652885261, 602806544261995,
    22294942654129813, 44587975059606459, 1207523353878597, 142551, 808815, 2130219,
    69915, 832593, 151305, 2130219, 1661751, 832593,
    30283623, 857079, 808815, 2130219, 151305, 857079,
    151305, 2137317, 1661751, 77013
  ]
def negativeCoefficients : Array ℕ := #[
    3816535449780536979578123452416, 3816536525739919467899636416512, 107433920442598371092651311104, 190750678650770771306958815232, 667440055048566065628341862400, 190750678650770771306958815232,
    21566211379944541578583867392, 1350749701049563614448694853632, 5197781193871703646960353280, 5356091882464512939669848064, 143752519991453691852965806080, 110451582021803279679536234496,
    1350749834928526852653607550976, 143752519991453691852965806080, 5197781193871703646960353280, 5132763912695814412805603328, 4761751063147795229838409728, 5132763912695814412805603328,
    110451582021803279679536234496, 4761751063147795229838409728, 21566077500981303373671170048, 5356091882464512939669848064, 38585382428951361586781487104, 5180046117869677723165042671616,
    30095226027077756418105802752, 53686373101028512559714936029184, 20595789168000904020558348288, 1102767021079719550302289920, 30095226027077756418105802752, 26011021261237183580007825408,
    20595789168000904020558348288, 406226956242230265086616797184, 26341284683583155087672868864, 5180047030362551929266096832512, 30095226027077756418105802752, 1102767021079719550302289920,
    26341284683583155087672868864, 1102767021079719550302289920, 30157107917469280248986075136, 26011021261237183580007825408, 38697868332185456921024659456, 1357399664057408542849378549760,
    50203747714692801454982115098624, 50201596965912154481718686908416, 1359550431642205256250480918528, 1346356128999101589715156992, 30556166774737696748124241920, 40238699227088371029897117696,
    1320657010599324980462223360, 31454474216575092139254349824, 1429035321381183338116546560, 40238699227088371029897117696, 31389588901100463214018166784, 31454474216575092139254349824,
    572041464940241175181296402432, 32379529142171461200874831872, 30556166774737696748124241920, 40238699227088371029897117696, 1429035321381183338116546560, 32379529142171461200874831872,
    1429035321381183338116546560, 40372776656270005996804374528, 31389588901100463214018166784, 1454734439780959947369480192
  ]
def negativeScales : Array ℕ := #[
    37, 40, 35, 37, 38, 37,
    43, 49, 31, 30, 34, 35,
    45, 34, 31, 30, 30, 30,
    35, 30, 39, 30, 44, 52,
    18, 50, 18, 13, 18, 18,
    18, 22, 14, 51, 18, 13,
    14, 13, 17, 18, 42, 49,
    54, 55, 50, 17, 19, 21,
    16, 19, 17, 21, 20, 19,
    24, 19, 19, 21, 17, 19,
    17, 21, 20, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37590106438448484, 40590106845173658, 35439364323530016, 37267602941607783, 38074553021241310, 37267602941607783,
    43122759411766446, 49091603209286301, 31069954465264788, 30113239271918783, 34859502000628696, 35479328834606682,
    45091603352278380, 34859502000628696, 31069954465264788, 30051794465636814, 30943550772056626, 30051794465636814,
    35479328834606682, 30943550772056626, 39122750455760569, 30113239271918783, 44962041074314692, 52030807788881292,
    18603521308843975, 50404326885317053, 18056336063797573, 13833186591641834, 18603521308843975, 18393109701248078,
    18056336063797573, 22358200728311561, 14411312365441260, 51030808043019729, 18603521308843975, 13833186591641834,
    14411312365441260, 13833186591641834, 17606484736879050, 18393109701248078, 42966240768384959, 49098688407805852,
    54307566007030646, 55307504200069863, 50100972514813740, 17121118634301809, 19625450227654563, 21022570325584000,
    16093314393147463, 19667251903584665, 17207100137840871, 21022570325584000, 20664272791428176, 19667251903584665,
    24852034479376090, 19709068663292793, 19625450227654563, 21022570325584000, 17207100137840871, 19709068663292793,
    17207100137840871, 21027369469091250, 20664272791428176, 16232814376688060
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
noncomputable def negativeCeiling : ℝ := 113238491123 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3816535449780536979578123452416, coefficient := (-3816535449780536979578123452416) }, { argument := 3816536525739919467899636416512, coefficient := (-3816536525739919467899636416512) }, { argument := 107433920442598371092651311104, coefficient := (-107433920442598371092651311104) }, { argument := 190750678650770771306958815232, coefficient := (-190750678650770771306958815232) }, { argument := 667440055048566065628341862400, coefficient := (-667440055048566065628341862400) }, { argument := 190750678650770771306958815232, coefficient := (-190750678650770771306958815232) }, { argument := 21566211379944541578583867392, coefficient := (-21566211379944541578583867392) }, { argument := 1350749701049563614448694853632, coefficient := (-1350749701049563614448694853632) }, { argument := 5197781193871703646960353280, coefficient := (-5197781193871703646960353280) }, { argument := 5356091882464512939669848064, coefficient := (-5356091882464512939669848064) }, { argument := 143752519991453691852965806080, coefficient := (-143752519991453691852965806080) }, { argument := 110451582021803279679536234496, coefficient := (-110451582021803279679536234496) }, { argument := 1350749834928526852653607550976, coefficient := (-1350749834928526852653607550976) }, { argument := 143752519991453691852965806080, coefficient := (-143752519991453691852965806080) }, { argument := 5197781193871703646960353280, coefficient := (-5197781193871703646960353280) }, { argument := 5132763912695814412805603328, coefficient := (-5132763912695814412805603328) }, { argument := 4761751063147795229838409728, coefficient := (-4761751063147795229838409728) }, { argument := 5132763912695814412805603328, coefficient := (-5132763912695814412805603328) }, { argument := 110451582021803279679536234496, coefficient := (-110451582021803279679536234496) }, { argument := 4761751063147795229838409728, coefficient := (-4761751063147795229838409728) }, { argument := 21566077500981303373671170048, coefficient := (-21566077500981303373671170048) }, { argument := 5356091882464512939669848064, coefficient := (-5356091882464512939669848064) }, { argument := 38585382428951361586781487104, coefficient := (-38585382428951361586781487104) }, { argument := 5180046117869677723165042671616, coefficient := (-5180046117869677723165042671616) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 53686373101028512559714936029184, coefficient := (-53686373101028512559714936029184) }, { argument := 20595789168000904020558348288, coefficient := (-20595789168000904020558348288) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 26011021261237183580007825408, coefficient := (-26011021261237183580007825408) }, { argument := 20595789168000904020558348288, coefficient := (-20595789168000904020558348288) }, { argument := 406226956242230265086616797184, coefficient := (-406226956242230265086616797184) }, { argument := 26341284683583155087672868864, coefficient := (-26341284683583155087672868864) }, { argument := 5180047030362551929266096832512, coefficient := (-5180047030362551929266096832512) }, { argument := 30095226027077756418105802752, coefficient := (-30095226027077756418105802752) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 26341284683583155087672868864, coefficient := (-26341284683583155087672868864) }, { argument := 1102767021079719550302289920, coefficient := (-1102767021079719550302289920) }, { argument := 30157107917469280248986075136, coefficient := (-30157107917469280248986075136) }, { argument := 26011021261237183580007825408, coefficient := (-26011021261237183580007825408) }, { argument := 38697868332185456921024659456, coefficient := (-38697868332185456921024659456) }, { argument := 1357399664057408542849378549760, coefficient := (-1357399664057408542849378549760) }, { argument := 50203747714692801454982115098624, coefficient := (-50203747714692801454982115098624) }, { argument := 50201596965912154481718686908416, coefficient := (-50201596965912154481718686908416) }, { argument := 1359550431642205256250480918528, coefficient := (-1359550431642205256250480918528) }, { argument := 1346356128999101589715156992, coefficient := (-1346356128999101589715156992) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1320657010599324980462223360, coefficient := (-1320657010599324980462223360) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 572041464940241175181296402432, coefficient := (-572041464940241175181296402432) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40372776656270005996804374528, coefficient := (-40372776656270005996804374528) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 1454734439780959947369480192, coefficient := (-1454734439780959947369480192) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
