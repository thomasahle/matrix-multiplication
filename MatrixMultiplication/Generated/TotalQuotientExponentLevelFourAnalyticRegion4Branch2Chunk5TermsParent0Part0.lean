import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5

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
def constantNumerator : ℤ := (-141575070997402540496254197039104)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1071975369145, 49592907229925, 24791040127611, 269682796955, 63073500579, 2119062147291,
    25715610536049, 4238162352063, 132696636003, 63073500579, 2305618305047, 4611237120137,
    126144232451, 953167317675, 176349780815813, 176311354019209, 1918244252675, 2305618305047,
    19312230525107, 117073796838569, 154499207040639, 4844894822699, 2119062147291, 19312230525107,
    154497866055733, 4238034819197, 1071975369145, 953167317675, 1071854242715, 1071854242715,
    24793582367403, 49576339295617, 539304247495, 4611237120137, 154497866055733, 1873181023453427,
    77249614448271, 4844895332657, 25715610536049, 117073796838569, 1873181023453427, 51430147384219,
    49592907229925, 176349780815813, 24793582367403, 126144232451, 4238034819197, 51430147384219,
    1059518219049, 132693752641, 4238162352063, 154499207040639, 77249614448271, 1059518219049,
    24791040127611, 176311354019209, 49576339295617, 132696636003, 4844894822699, 4844895332657,
    132693752641, 269682796955, 1918244252675, 539304247495
  ]
def negativeCoefficients : Array ℕ := #[
    301734242064485743455109120, 13959162407556862937189580800, 13956114885104489150527045632, 303635835968692783331409920, 35507224213067145462939648, 1192925937114333838722465792,
    14476601753469384661860876288, 1192936649342911979955683328, 37350782528526821483347968, 35507224213067145462939648, 1297947717433532972126961664, 1297947860997874518560079872,
    35506444891328801832697856, 1073170994175716296438579200, 49638050448060254430930403328, 49627234266381078415858991104, 1079875512694090696858009600, 1297947717433532972126961664,
    43487277098282501747859521536, 527253507817028501047265460224, 43487660703578682028336349184, 1363716657384778855343980544, 1192925937114333838722465792, 43487277098282501747859521536,
    43487283249883496337110990848, 1192900752032424786743263232, 301734242064485743455109120, 1073170994175716296438579200, 301700148005422448550871040, 301700148005422448550871040,
    13957546038876981356434292736, 13954498948633374958657994752, 303601301007225968855613440, 1297947860997874518560079872, 43487283249883496337110990848, 527253584951396135346070618112,
    43487666855468469943692951552, 1363716800925195028756692992, 14476601753469384661860876288, 527253507817028501047265460224, 527253584951396135346070618112, 14476299537198648623223537664,
    13959162407556862937189580800, 49638050448060254430930403328, 13957546038876981356434292736, 35506444891328801832697856, 1192900752032424786743263232, 14476299537198648623223537664,
    1192911464125331989201944576, 37349970934275023092842496, 1192936649342911979955683328, 43487660703578682028336349184, 43487666855468469943692951552, 1192911464125331989201944576,
    13956114885104489150527045632, 49627234266381078415858991104, 13954498948633374958657994752, 37350782528526821483347968, 1363716657384778855343980544, 1363716800925195028756692992,
    37349970934275023092842496, 303635835968692783331409920, 1079875512694090696858009600, 303601301007225968855613440
  ]
def negativeScales : Array ℕ := #[
    39, 45, 44, 37, 35, 40,
    44, 41, 36, 35, 41, 42,
    36, 39, 47, 47, 40, 41,
    44, 46, 47, 42, 40, 44,
    47, 41, 39, 39, 39, 39,
    44, 45, 38, 42, 47, 50,
    46, 42, 44, 46, 50, 45,
    45, 47, 44, 36, 41, 45,
    39, 36, 41, 47, 46, 39,
    44, 47, 45, 36, 42, 42,
    36, 37, 40, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39963408908967174, 45495199034875544, 44494884035636923, 37972472554023332, 35876314956711648, 40946563047790445,
    44547709639876514, 41946576002837991, 36949340851429519, 35876314956711648, 41068290833340136, 42068290992914785,
    36876283291718689, 39793938529392602, 47325433111070504, 47325118712098566, 40802923571727220, 41068290833340136,
    44134580035922089, 46734411540192322, 47134592762012442, 42139602485317065, 40946563047790445, 44134580035922089,
    47134580240002091, 41946532589250435, 39963408908967174, 39793938529392602, 39963245884315436, 39963245884315436,
    44495031971692876, 45494716980655633, 38972308455264954, 42068290992914785, 47134580240002091, 50734411751250874,
    46134592966100225, 42139602637170483, 44547709639876514, 46734411540192322, 50734411751250874, 45547679521588145,
    45495199034875544, 47325433111070504, 44495031971692876, 36876283291718689, 41946532589250435, 45547679521588145,
    39946545544407414, 36949309502797759, 41946576002837991, 47134592762012442, 46134592966100225, 39946545544407414,
    44494884035636923, 47325118712098566, 45494716980655633, 36949340851429519, 42139602485317065, 42139602637170483,
    36949309502797759, 37972472554023332, 40802923571727220, 38972308455264954
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
noncomputable def negativeCeiling : ℝ := 1648809341 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 301734242064485743455109120, coefficient := (-301734242064485743455109120) }, { argument := 13959162407556862937189580800, coefficient := (-13959162407556862937189580800) }, { argument := 13956114885104489150527045632, coefficient := (-13956114885104489150527045632) }, { argument := 303635835968692783331409920, coefficient := (-303635835968692783331409920) }, { argument := 35507224213067145462939648, coefficient := (-35507224213067145462939648) }, { argument := 1192925937114333838722465792, coefficient := (-1192925937114333838722465792) }, { argument := 14476601753469384661860876288, coefficient := (-14476601753469384661860876288) }, { argument := 1192936649342911979955683328, coefficient := (-1192936649342911979955683328) }, { argument := 37350782528526821483347968, coefficient := (-37350782528526821483347968) }, { argument := 35507224213067145462939648, coefficient := (-35507224213067145462939648) }, { argument := 1297947717433532972126961664, coefficient := (-1297947717433532972126961664) }, { argument := 1297947860997874518560079872, coefficient := (-1297947860997874518560079872) }, { argument := 35506444891328801832697856, coefficient := (-35506444891328801832697856) }, { argument := 1073170994175716296438579200, coefficient := (-1073170994175716296438579200) }, { argument := 49638050448060254430930403328, coefficient := (-49638050448060254430930403328) }, { argument := 49627234266381078415858991104, coefficient := (-49627234266381078415858991104) }, { argument := 1079875512694090696858009600, coefficient := (-1079875512694090696858009600) }, { argument := 1297947717433532972126961664, coefficient := (-1297947717433532972126961664) }, { argument := 43487277098282501747859521536, coefficient := (-43487277098282501747859521536) }, { argument := 527253507817028501047265460224, coefficient := (-527253507817028501047265460224) }, { argument := 43487660703578682028336349184, coefficient := (-43487660703578682028336349184) }, { argument := 1363716657384778855343980544, coefficient := (-1363716657384778855343980544) }, { argument := 1192925937114333838722465792, coefficient := (-1192925937114333838722465792) }, { argument := 43487277098282501747859521536, coefficient := (-43487277098282501747859521536) }, { argument := 43487283249883496337110990848, coefficient := (-43487283249883496337110990848) }, { argument := 1192900752032424786743263232, coefficient := (-1192900752032424786743263232) }, { argument := 301734242064485743455109120, coefficient := (-301734242064485743455109120) }, { argument := 1073170994175716296438579200, coefficient := (-1073170994175716296438579200) }, { argument := 301700148005422448550871040, coefficient := (-301700148005422448550871040) }, { argument := 301700148005422448550871040, coefficient := (-301700148005422448550871040) }, { argument := 13957546038876981356434292736, coefficient := (-13957546038876981356434292736) }, { argument := 13954498948633374958657994752, coefficient := (-13954498948633374958657994752) }, { argument := 303601301007225968855613440, coefficient := (-303601301007225968855613440) }, { argument := 1297947860997874518560079872, coefficient := (-1297947860997874518560079872) }, { argument := 43487283249883496337110990848, coefficient := (-43487283249883496337110990848) }, { argument := 527253584951396135346070618112, coefficient := (-527253584951396135346070618112) }, { argument := 43487666855468469943692951552, coefficient := (-43487666855468469943692951552) }, { argument := 1363716800925195028756692992, coefficient := (-1363716800925195028756692992) }, { argument := 14476601753469384661860876288, coefficient := (-14476601753469384661860876288) }, { argument := 527253507817028501047265460224, coefficient := (-527253507817028501047265460224) }, { argument := 527253584951396135346070618112, coefficient := (-527253584951396135346070618112) }, { argument := 14476299537198648623223537664, coefficient := (-14476299537198648623223537664) }, { argument := 13959162407556862937189580800, coefficient := (-13959162407556862937189580800) }, { argument := 49638050448060254430930403328, coefficient := (-49638050448060254430930403328) }, { argument := 13957546038876981356434292736, coefficient := (-13957546038876981356434292736) }, { argument := 35506444891328801832697856, coefficient := (-35506444891328801832697856) }, { argument := 1192900752032424786743263232, coefficient := (-1192900752032424786743263232) }, { argument := 14476299537198648623223537664, coefficient := (-14476299537198648623223537664) }, { argument := 1192911464125331989201944576, coefficient := (-1192911464125331989201944576) }, { argument := 37349970934275023092842496, coefficient := (-37349970934275023092842496) }, { argument := 1192936649342911979955683328, coefficient := (-1192936649342911979955683328) }, { argument := 43487660703578682028336349184, coefficient := (-43487660703578682028336349184) }, { argument := 43487666855468469943692951552, coefficient := (-43487666855468469943692951552) }, { argument := 1192911464125331989201944576, coefficient := (-1192911464125331989201944576) }, { argument := 13956114885104489150527045632, coefficient := (-13956114885104489150527045632) }, { argument := 49627234266381078415858991104, coefficient := (-49627234266381078415858991104) }, { argument := 13954498948633374958657994752, coefficient := (-13954498948633374958657994752) }, { argument := 37350782528526821483347968, coefficient := (-37350782528526821483347968) }, { argument := 1363716657384778855343980544, coefficient := (-1363716657384778855343980544) }, { argument := 1363716800925195028756692992, coefficient := (-1363716800925195028756692992) }, { argument := 37349970934275023092842496, coefficient := (-37349970934275023092842496) }, { argument := 303635835968692783331409920, coefficient := (-303635835968692783331409920) }, { argument := 1079875512694090696858009600, coefficient := (-1079875512694090696858009600) }, { argument := 303601301007225968855613440, coefficient := (-303601301007225968855613440) }] }

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
def constantNumerator : ℤ := 125537282327314036036485261557760
def positiveArguments : Array ℕ := #[
    9, 3019741, 21476167, 6038783, 1793097, 65315781,
    130631581, 3586119, 141185, 9461399, 114715789, 18922965,
    593375, 355035, 16422859, 8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 57041294741389061229006290944, 202836662442622279680171966464, 57034692873046009464997543936, 33870644693336448894970626048, 1233780219987415993301864546304,
    1233780399437342342348382666752, 33869936338364018448188571648, 5333818495071606875965358080, 178720774074625513420872482816, 2166919988118185339356840984576, 178722351345030791882373857280,
    5604268423545551457353728000, 3353210768491248976889118720, 155109517788988197449108553728, 155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    3, 21, 24, 22, 20, 25,
    26, 21, 17, 23, 26, 24,
    19, 18, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2535301200456458802993406410752, 2535301200456458802993406410752, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 21525993385748905, 24356233192751916, 22525826400865778, 20774022104151685, 25960928268071444,
    26960928477907436, 21773991931980443, 17107227294100077, 23173622091275279, 26773488730589481, 24173634823483735,
    19178584619091518, 18437601729582122, 23969201966206902, 22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 946733739 / 500000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 57041294741389061229006290944, coefficient := 57041294741389061229006290944 }, { argument := 202836662442622279680171966464, coefficient := 202836662442622279680171966464 }, { argument := 57034692873046009464997543936, coefficient := 57034692873046009464997543936 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 33870644693336448894970626048, coefficient := 33870644693336448894970626048 }, { argument := 1233780219987415993301864546304, coefficient := 1233780219987415993301864546304 }, { argument := 1233780399437342342348382666752, coefficient := 1233780399437342342348382666752 }, { argument := 33869936338364018448188571648, coefficient := 33869936338364018448188571648 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 5333818495071606875965358080, coefficient := 5333818495071606875965358080 }, { argument := 178720774074625513420872482816, coefficient := 178720774074625513420872482816 }, { argument := 2166919988118185339356840984576, coefficient := 2166919988118185339356840984576 }, { argument := 178722351345030791882373857280, coefficient := 178722351345030791882373857280 }, { argument := 5604268423545551457353728000, coefficient := 5604268423545551457353728000 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5
