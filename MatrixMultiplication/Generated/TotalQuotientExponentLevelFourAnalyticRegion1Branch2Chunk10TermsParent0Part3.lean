import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1267490578038590483432314081640448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    123520859883, 2251633042425, 1125816439407, 123521445735, 156057023371771, 269271949026821,
    156057023371771, 553057955, 1243713485, 79597671495, 2212232685, 197872055199,
    349929213025, 197872055199, 19809700467, 19809695117, 5151, 29715,
    37947, 1245, 60861, 5355, 37947, 14469,
    60861, 136281, 29979, 29715, 37947, 5355,
    29979, 5355, 76167, 14469, 2763, 7515,
    22275, 432315, 14175, 361935, 15075, 432315,
    316485, 361935, 6322905, 20655, 22275, 432315,
    15075, 20655, 15075, 217035, 316485, 7965,
    4370166951, 78647538669, 39323773329, 4370169147, 5151, 29715,
    37947, 1245, 60861, 5355
  ]
def negativeCoefficients : Array ℕ := #[
    142409855626639884324918263808, 5191912310190247020114581913600, 5191911932928966439652900732928, 142410531068009201255432847360, 1405636704611313321721129336832, 4850772197194072994489632292864,
    1405636704611313321721129336832, 5101059276907086940355952640, 183539714870531226544981934080, 183539734366433869446764298240, 5101061271461289910201221120, 228130947599680157628418228224,
    806881829573345748676562124800, 228130947599680157628418228224, 91356118672898396767458951168, 91356094000378198180933664768, 48649819506523084991496192, 1122600960307772060199813120,
    1433597127403635415392976896, 47034770169381666328412160, 1149631786055717909403009024, 50576545031533900238684160, 1433597127403635415392976896, 1093246730250254345551478784,
    1149631786055717909403009024, 20594202452862659819766546432, 1132574598319592750891139072, 1122600960307772060199813120, 1433597127403635415392976896, 50576545031533900238684160,
    1132574598319592750891139072, 50576545031533900238684160, 1438753951602929067966332928, 1093246730250254345551478784, 52191594368675318901768192, 1135634691800492280989614080,
    26928822631915864866580070400, 32664797856668650728943779840, 1071032718314835534466252800, 27347035407638800646704988160, 1139034795668158425543475200, 32664797856668650728943779840,
    23912930501295994647305256960, 27347035407638800646704988160, 477745194341902305118472110080, 24970362804140165603556065280, 26928822631915864866580070400, 32664797856668650728943779840,
    1139034795668158425543475200, 24970362804140165603556065280, 1139034795668158425543475200, 32797401907507630366544363520, 23912930501295994647305256960, 1203636769153815172066836480,
    5038459456530036902829490176, 181348877231777318374251429888, 181348895653157118982452412416, 5038461988345661019465449472, 48649819506523084991496192, 1122600960307772060199813120,
    1433597127403635415392976896, 47034770169381666328412160, 1149631786055717909403009024, 50576545031533900238684160
  ]
def negativeScales : Array ℕ := #[
    36, 41, 40, 36, 47, 47,
    47, 29, 30, 36, 31, 37,
    38, 37, 34, 34, 12, 14,
    15, 10, 15, 12, 15, 13,
    15, 17, 14, 14, 15, 12,
    14, 12, 16, 13, 11, 12,
    14, 18, 13, 18, 13, 18,
    18, 18, 22, 14, 14, 18,
    13, 14, 13, 17, 18, 12,
    32, 36, 35, 32, 12, 14,
    15, 10, 15, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36845963746352264, 41034108863486040, 40034108758655109, 36845970588951948, 47149066615866750, 47936057283870891,
    47149066615866750, 29042855427642279, 30212007023234312, 36212007176479840, 31042855991747250, 37525776923592611,
    38348272153400307, 37525776923592611, 34205488014964692, 34205487625336413, 12330636824723291, 14858903762549026,
    15211698213643360, 10281930026955444, 15893230422217317, 12386670859637623, 15211698213643360, 13820677596462139,
    15893230422217317, 17056224913201407, 14871664642721115, 14858903762549026, 15211698213643360, 12386670859637623,
    14871664642721115, 12386670859637623, 16216878452749041, 13820677596462139, 11432019846812516, 12875557391602924,
    14443137811296683, 18721723368736596, 13791061115254762, 18465371101033474, 13879870384705585, 18721723368736596,
    18271777598297583, 18465371101033474, 22592156112886414, 14334203439743484, 14443137811296683, 18721723368736596,
    13879870384705585, 14334203439743484, 13879870384705585, 17727568191228207, 18271777598297583, 12959458658631210,
    32025041249222205, 36194682565047429, 35194682711596073, 32025041974173345, 12330636824723291, 14858903762549026,
    15211698213643360, 10281930026955444, 15893230422217317, 12386670859637623
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
noncomputable def negativeCeiling : ℝ := 10759513569 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 142409855626639884324918263808, coefficient := (-142409855626639884324918263808) }, { argument := 5191912310190247020114581913600, coefficient := (-5191912310190247020114581913600) }, { argument := 5191911932928966439652900732928, coefficient := (-5191911932928966439652900732928) }, { argument := 142410531068009201255432847360, coefficient := (-142410531068009201255432847360) }, { argument := 1405636704611313321721129336832, coefficient := (-1405636704611313321721129336832) }, { argument := 4850772197194072994489632292864, coefficient := (-4850772197194072994489632292864) }, { argument := 1405636704611313321721129336832, coefficient := (-1405636704611313321721129336832) }, { argument := 5101059276907086940355952640, coefficient := (-5101059276907086940355952640) }, { argument := 183539714870531226544981934080, coefficient := (-183539714870531226544981934080) }, { argument := 183539734366433869446764298240, coefficient := (-183539734366433869446764298240) }, { argument := 5101061271461289910201221120, coefficient := (-5101061271461289910201221120) }, { argument := 228130947599680157628418228224, coefficient := (-228130947599680157628418228224) }, { argument := 806881829573345748676562124800, coefficient := (-806881829573345748676562124800) }, { argument := 228130947599680157628418228224, coefficient := (-228130947599680157628418228224) }, { argument := 91356118672898396767458951168, coefficient := (-91356118672898396767458951168) }, { argument := 91356094000378198180933664768, coefficient := (-91356094000378198180933664768) }, { argument := 48649819506523084991496192, coefficient := (-48649819506523084991496192) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 47034770169381666328412160, coefficient := (-47034770169381666328412160) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 20594202452862659819766546432, coefficient := (-20594202452862659819766546432) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1438753951602929067966332928, coefficient := (-1438753951602929067966332928) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 52191594368675318901768192, coefficient := (-52191594368675318901768192) }, { argument := 1135634691800492280989614080, coefficient := (-1135634691800492280989614080) }, { argument := 26928822631915864866580070400, coefficient := (-26928822631915864866580070400) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 1071032718314835534466252800, coefficient := (-1071032718314835534466252800) }, { argument := 27347035407638800646704988160, coefficient := (-27347035407638800646704988160) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 23912930501295994647305256960, coefficient := (-23912930501295994647305256960) }, { argument := 27347035407638800646704988160, coefficient := (-27347035407638800646704988160) }, { argument := 477745194341902305118472110080, coefficient := (-477745194341902305118472110080) }, { argument := 24970362804140165603556065280, coefficient := (-24970362804140165603556065280) }, { argument := 26928822631915864866580070400, coefficient := (-26928822631915864866580070400) }, { argument := 32664797856668650728943779840, coefficient := (-32664797856668650728943779840) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 24970362804140165603556065280, coefficient := (-24970362804140165603556065280) }, { argument := 1139034795668158425543475200, coefficient := (-1139034795668158425543475200) }, { argument := 32797401907507630366544363520, coefficient := (-32797401907507630366544363520) }, { argument := 23912930501295994647305256960, coefficient := (-23912930501295994647305256960) }, { argument := 1203636769153815172066836480, coefficient := (-1203636769153815172066836480) }, { argument := 5038459456530036902829490176, coefficient := (-5038459456530036902829490176) }, { argument := 181348877231777318374251429888, coefficient := (-181348877231777318374251429888) }, { argument := 181348895653157118982452412416, coefficient := (-181348895653157118982452412416) }, { argument := 5038461988345661019465449472, coefficient := (-5038461988345661019465449472) }, { argument := 48649819506523084991496192, coefficient := (-48649819506523084991496192) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 47034770169381666328412160, coefficient := (-47034770169381666328412160) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }] }

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
def constantNumerator : ℤ := (-436184659354164634377362874564608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37947, 14469, 60861, 136281, 29979, 29715,
    37947, 5355, 29979, 5355, 76167, 14469,
    2763, 4048367511, 72705726069, 72705735513, 4048366797, 7505674305,
    13172244415, 7505674305, 71463, 405195, 534261, 17535,
    834393, 75915, 534261, 52143, 834393, 3795981,
    430227, 405195, 534261, 75915, 430227, 75915,
    1072071, 52143, 38619, 4370166951, 78647538669, 39323773329,
    4370169147, 117801, 704865, 1679769, 55065, 713793,
    116655, 1679769, 1211301, 713793, 24724773, 634329,
    704865, 1679769, 116655, 634329, 116655, 1686867,
    1211301, 62163, 5824026477, 206894801301
  ]
def negativeCoefficients : Array ℕ := #[
    1433597127403635415392976896, 1093246730250254345551478784, 1149631786055717909403009024, 20594202452862659819766546432, 1132574598319592750891139072, 1122600960307772060199813120,
    1433597127403635415392976896, 50576545031533900238684160, 1132574598319592750891139072, 50576545031533900238684160, 1438753951602929067966332928, 1093246730250254345551478784,
    52191594368675318901768192, 4667449961983596125786996736, 167647990186009475557714034688, 167648011962390854571839717376, 4667449138797641836498255872, 8653453312809550474830151680,
    30373127699981873700751278080, 8653453312809550474830151680, 1349897903861253823625428992, 30615668592421854277816811520, 40367619832070712344231018496, 1324907140433907661154549760,
    31522476293928415030331572224, 1433993806188196465590927360, 40367619832070712344231018496, 31518509506082804528352067584, 31522476293928415030331572224, 573632430208319958653790584832,
    32507033037208941621644623872, 30615668592421854277816811520, 40367619832070712344231018496, 1433993806188196465590927360, 32507033037208941621644623872, 1433993806188196465590927360,
    40501697261252347311138275328, 31518509506082804528352067584, 1458984569615542628061806592, 5038459456530036902829490176, 181348877231777318374251429888, 181348895653157118982452412416,
    5038461988345661019465449472, 1112598988097054151637204992, 26629046807583299788414648320, 31729939298253844283859664896, 1040148441516868054768680960, 26966337111255781328157671424,
    1101775324118316924807413760, 31729939298253844283859664896, 22880828972265936467980713984, 26966337111255781328157671424, 467037757247041465996680364032, 23964272069697753430068559872,
    26629046807583299788414648320, 31729939298253844283859664896, 1101775324118316924807413760, 23964272069697753430068559872, 1101775324118316924807413760, 31864016727435479250766921728,
    22880828972265936467980713984, 1174225870698503021675937792, 107434325899727268219382136832, 3816535449780536979578123452416
  ]
def negativeScales : Array ℕ := #[
    15, 13, 15, 17, 14, 14,
    15, 12, 14, 12, 16, 13,
    11, 31, 36, 36, 31, 32,
    33, 32, 16, 18, 19, 14,
    19, 16, 19, 15, 19, 21,
    18, 18, 19, 16, 18, 16,
    20, 15, 15, 32, 36, 35,
    32, 16, 19, 20, 15, 19,
    16, 20, 20, 19, 24, 19,
    19, 20, 16, 19, 16, 20,
    20, 15, 32, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15211698213643360, 13820677596462139, 15893230422217317, 17056224913201407, 14871664642721115, 14858903762549026,
    15211698213643360, 12386670859637623, 14871664642721115, 12386670859637623, 16216878452749041, 13820677596462139,
    11432019846812516, 31914693123560199, 36081349939511448, 36081350126908120, 31914692869115796, 32805334543178402,
    33616782135821942, 32805334543178402, 16124908858743769, 18628256846219509, 19027185181546657, 14097949810140175,
    19670367529132881, 16212097354617241, 19027185181546657, 15670185968990918, 19670367529132881, 21856041342531762,
    18714738542172370, 18628256846219509, 19027185181546657, 16212097354617241, 18714738542172370, 16212097354617241,
    20031969023586250, 15670185968990918, 15237023187190699, 32025041249222205, 36194682565047429, 35194682711596073,
    32025041974173345, 16845992262144210, 19426987444741877, 20679831418165570, 15748847994927351, 19445146227722351,
    16831888620276083, 20679831418165570, 20208125978740077, 19445146227722351, 24559453939766844, 19274871774671289,
    19426987444741877, 20679831418165570, 16831888620276083, 19274871774671289, 16831888620276083, 20685914799074640,
    20208125978740077, 15923768516401456, 32439369768271146, 37590106438448484
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
noncomputable def negativeCeiling : ℝ := 64167047 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 20594202452862659819766546432, coefficient := (-20594202452862659819766546432) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1438753951602929067966332928, coefficient := (-1438753951602929067966332928) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 52191594368675318901768192, coefficient := (-52191594368675318901768192) }, { argument := 4667449961983596125786996736, coefficient := (-4667449961983596125786996736) }, { argument := 167647990186009475557714034688, coefficient := (-167647990186009475557714034688) }, { argument := 167648011962390854571839717376, coefficient := (-167648011962390854571839717376) }, { argument := 4667449138797641836498255872, coefficient := (-4667449138797641836498255872) }, { argument := 8653453312809550474830151680, coefficient := (-8653453312809550474830151680) }, { argument := 30373127699981873700751278080, coefficient := (-30373127699981873700751278080) }, { argument := 8653453312809550474830151680, coefficient := (-8653453312809550474830151680) }, { argument := 1349897903861253823625428992, coefficient := (-1349897903861253823625428992) }, { argument := 30615668592421854277816811520, coefficient := (-30615668592421854277816811520) }, { argument := 40367619832070712344231018496, coefficient := (-40367619832070712344231018496) }, { argument := 1324907140433907661154549760, coefficient := (-1324907140433907661154549760) }, { argument := 31522476293928415030331572224, coefficient := (-31522476293928415030331572224) }, { argument := 1433993806188196465590927360, coefficient := (-1433993806188196465590927360) }, { argument := 40367619832070712344231018496, coefficient := (-40367619832070712344231018496) }, { argument := 31518509506082804528352067584, coefficient := (-31518509506082804528352067584) }, { argument := 31522476293928415030331572224, coefficient := (-31522476293928415030331572224) }, { argument := 573632430208319958653790584832, coefficient := (-573632430208319958653790584832) }, { argument := 32507033037208941621644623872, coefficient := (-32507033037208941621644623872) }, { argument := 30615668592421854277816811520, coefficient := (-30615668592421854277816811520) }, { argument := 40367619832070712344231018496, coefficient := (-40367619832070712344231018496) }, { argument := 1433993806188196465590927360, coefficient := (-1433993806188196465590927360) }, { argument := 32507033037208941621644623872, coefficient := (-32507033037208941621644623872) }, { argument := 1433993806188196465590927360, coefficient := (-1433993806188196465590927360) }, { argument := 40501697261252347311138275328, coefficient := (-40501697261252347311138275328) }, { argument := 31518509506082804528352067584, coefficient := (-31518509506082804528352067584) }, { argument := 1458984569615542628061806592, coefficient := (-1458984569615542628061806592) }, { argument := 5038459456530036902829490176, coefficient := (-5038459456530036902829490176) }, { argument := 181348877231777318374251429888, coefficient := (-181348877231777318374251429888) }, { argument := 181348895653157118982452412416, coefficient := (-181348895653157118982452412416) }, { argument := 5038461988345661019465449472, coefficient := (-5038461988345661019465449472) }, { argument := 1112598988097054151637204992, coefficient := (-1112598988097054151637204992) }, { argument := 26629046807583299788414648320, coefficient := (-26629046807583299788414648320) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 1040148441516868054768680960, coefficient := (-1040148441516868054768680960) }, { argument := 26966337111255781328157671424, coefficient := (-26966337111255781328157671424) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 22880828972265936467980713984, coefficient := (-22880828972265936467980713984) }, { argument := 26966337111255781328157671424, coefficient := (-26966337111255781328157671424) }, { argument := 467037757247041465996680364032, coefficient := (-467037757247041465996680364032) }, { argument := 23964272069697753430068559872, coefficient := (-23964272069697753430068559872) }, { argument := 26629046807583299788414648320, coefficient := (-26629046807583299788414648320) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 23964272069697753430068559872, coefficient := (-23964272069697753430068559872) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 31864016727435479250766921728, coefficient := (-31864016727435479250766921728) }, { argument := 22880828972265936467980713984, coefficient := (-22880828972265936467980713984) }, { argument := 1174225870698503021675937792, coefficient := (-1174225870698503021675937792) }, { argument := 107434325899727268219382136832, coefficient := (-107434325899727268219382136832) }, { argument := 3816535449780536979578123452416, coefficient := (-3816535449780536979578123452416) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
