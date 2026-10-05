import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-348892654240791420747556512071680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3015, 18830736977, 3015, 3015, 258285, 3015,
    100165, 258285, 1118881123, 3015, 3015, 6365,
    11187805119, 19080389907, 11187804699, 253, 253, 1995,
    3325, 101745, 3325, 104405, 3325, 101745,
    57855, 104405, 1629915, 1995, 3325, 101745,
    3325, 1995, 3325, 51205, 57855, 1995,
    14650956425, 98021, 244847211931, 1542541, 46431, 244847331869,
    46431, 46431, 3977589, 46431, 1542541, 3977589,
    14650836487, 46431, 46431, 98021, 11398368829, 2432128599,
    11398368339, 14356765321, 110751, 244713906587, 1742871, 52461,
    244714026525, 52461, 52461, 4494159
  ]
def negativeCoefficients : Array ℕ := #[
    56951739783407921277173760, 43420723216757258396687663104, 56951739783407921277173760, 56951739783407921277173760, 2439432854055972628038942720, 56951739783407921277173760,
    473015838756638012829859840, 2439432854055972628038942720, 1289982107805358617996034048, 56951739783407921277173760, 56951739783407921277173760, 60115725326930583570350080,
    51594644444182658722169880576, 175985534720509896351710969856, 51594642507274530982666960896, 9787463435600037798421200896, 9787463435600037798421200896, 75368969066599537610588160,
    2009839175109321002949017600, 1921908711198288209069998080, 62807474222166281342156800, 1972154690576021234143723520, 62807474222166281342156800, 1921908711198288209069998080,
    1092850051465693295353528320, 1972154690576021234143723520, 30788223863705911113925263360, 1205903505065592601769410560, 2009839175109321002949017600, 1921908711198288209069998080,
    62807474222166281342156800, 1205903505065592601769410560, 62807474222166281342156800, 1934470206042721465338429440, 1092850051465693295353528320, 75368969066599537610588160,
    33782805450880703604038041600, 1851564340069461973966782464, 1129158463913120217465433882624, 14568887833704450795159683072, 1754113585328963975336951808, 1129159017029517895609484312576,
    1754113585328963975336951808, 1754113585328963975336951808, 75134531904923956943599435776, 1754113585328963975336951808, 14568887833704450795159683072, 75134531904923956943599435776,
    33782528892681864532012826624, 1754113585328963975336951808, 1754113585328963975336951808, 1851564340069461973966782464, 52565698161577857884845244416, 179459415280411058018961063936,
    52565695901851708855425171456, 33104446950349444808381038592, 1046013620688592154124091392, 1128543701522013764181869723648, 8230475594365501423239561216, 990960272231297830222823424,
    1128544254638411442325920153600, 990960272231297830222823424, 990960272231297830222823424, 42446131660573923727877603328
  ]
def negativeScales : Array ℕ := #[
    11, 34, 11, 11, 17, 11,
    16, 17, 30, 11, 11, 12,
    33, 34, 33, 7, 7, 10,
    11, 16, 11, 16, 11, 16,
    15, 16, 20, 10, 11, 16,
    11, 10, 11, 15, 15, 10,
    33, 16, 37, 20, 15, 37,
    15, 15, 21, 15, 20, 21,
    33, 15, 15, 16, 33, 31,
    33, 33, 16, 37, 20, 15,
    37, 15, 15, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11557942286789136, 34132370412567510, 11557942286789136, 11557942286789136, 17978604352023330, 11557942286789136,
    16612018959551099, 17978604352023330, 30059409617406156, 11557942286789136, 11557942286789136, 12635944798803559,
    33381207977634033, 34151371601933388, 33381207923473997, 7982993592700323, 7982993592700323, 10962173043893966,
    11699138625346849, 16634598373095531, 11699138625346849, 16671831279316955, 11699138625346849, 16634598373095531,
    15820154027206250, 16671831279316955, 20636365299270394, 10962173043893966, 11699138625346849, 16634598373095531,
    11699138625346849, 10962173043893966, 11699138625346849, 15643997071101728, 15820154027206250, 10962173043893966,
    33770275797115989, 16580803244599554, 37833090813219177, 20556877405352415, 15502800732595284, 37833091519920790,
    15502800732595284, 15502800732595284, 21923462787679901, 15502800732595284, 20556877405352415, 21923462787679901,
    33770263986646943, 15502800732595284, 15502800732595284, 16580803244599554, 33408108330220798, 31179572367403674,
    33408108268201347, 33741011685612747, 16756960200011716, 37832305134124789, 20733034360659112, 15678957687792584,
    37832305841211370, 15678957687792584, 15678957687792584, 22099619736221536
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
noncomputable def negativeCeiling : ℝ := 2417032191 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 43420723216757258396687663104, coefficient := (-43420723216757258396687663104) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 1289982107805358617996034048, coefficient := (-1289982107805358617996034048) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 51594644444182658722169880576, coefficient := (-51594644444182658722169880576) }, { argument := 175985534720509896351710969856, coefficient := (-175985534720509896351710969856) }, { argument := 51594642507274530982666960896, coefficient := (-51594642507274530982666960896) }, { argument := 9787463435600037798421200896, coefficient := (-9787463435600037798421200896) }, { argument := 9787463435600037798421200896, coefficient := (-9787463435600037798421200896) }, { argument := 75368969066599537610588160, coefficient := (-75368969066599537610588160) }, { argument := 2009839175109321002949017600, coefficient := (-2009839175109321002949017600) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1972154690576021234143723520, coefficient := (-1972154690576021234143723520) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 1092850051465693295353528320, coefficient := (-1092850051465693295353528320) }, { argument := 1972154690576021234143723520, coefficient := (-1972154690576021234143723520) }, { argument := 30788223863705911113925263360, coefficient := (-30788223863705911113925263360) }, { argument := 1205903505065592601769410560, coefficient := (-1205903505065592601769410560) }, { argument := 2009839175109321002949017600, coefficient := (-2009839175109321002949017600) }, { argument := 1921908711198288209069998080, coefficient := (-1921908711198288209069998080) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1205903505065592601769410560, coefficient := (-1205903505065592601769410560) }, { argument := 62807474222166281342156800, coefficient := (-62807474222166281342156800) }, { argument := 1934470206042721465338429440, coefficient := (-1934470206042721465338429440) }, { argument := 1092850051465693295353528320, coefficient := (-1092850051465693295353528320) }, { argument := 75368969066599537610588160, coefficient := (-75368969066599537610588160) }, { argument := 33782805450880703604038041600, coefficient := (-33782805450880703604038041600) }, { argument := 1851564340069461973966782464, coefficient := (-1851564340069461973966782464) }, { argument := 1129158463913120217465433882624, coefficient := (-1129158463913120217465433882624) }, { argument := 14568887833704450795159683072, coefficient := (-14568887833704450795159683072) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 1129159017029517895609484312576, coefficient := (-1129159017029517895609484312576) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 75134531904923956943599435776, coefficient := (-75134531904923956943599435776) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 14568887833704450795159683072, coefficient := (-14568887833704450795159683072) }, { argument := 75134531904923956943599435776, coefficient := (-75134531904923956943599435776) }, { argument := 33782528892681864532012826624, coefficient := (-33782528892681864532012826624) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 1754113585328963975336951808, coefficient := (-1754113585328963975336951808) }, { argument := 1851564340069461973966782464, coefficient := (-1851564340069461973966782464) }, { argument := 52565698161577857884845244416, coefficient := (-52565698161577857884845244416) }, { argument := 179459415280411058018961063936, coefficient := (-179459415280411058018961063936) }, { argument := 52565695901851708855425171456, coefficient := (-52565695901851708855425171456) }, { argument := 33104446950349444808381038592, coefficient := (-33104446950349444808381038592) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1128543701522013764181869723648, coefficient := (-1128543701522013764181869723648) }, { argument := 8230475594365501423239561216, coefficient := (-8230475594365501423239561216) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 1128544254638411442325920153600, coefficient := (-1128544254638411442325920153600) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 42446131660573923727877603328, coefficient := (-42446131660573923727877603328) }] }

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

end TermShard10


end Parent3

namespace Parent3

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 310399361966718043860963878785515520
def positiveArguments : Array ℕ := #[
    40871, 1, 1, 1, 1, 1643,
    19663, 29415, 8533, 1643, 34079, 17119,
    1643, 19663, 1643
  ]
def positiveCoefficients : Array ℕ := #[
    3238134230120497741785734794182656, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 31780241946029371744675954688,
    760675468514638510791921238016, 568968847743429074783714672640, 660208897201384367857139187712, 31780241946029371744675954688, 659183728106351162316988350464, 662259235391450778937440862208,
    31780241946029371744675954688, 760675468514638510791921238016, 31780241946029371744675954688
  ]
def positiveScales : Array ℕ := #[
    15, 0, 0, 0, 0, 10,
    14, 14, 13, 10, 15, 14,
    10, 14, 10
  ]
def negativeArguments : Array ℕ := #[
    52461, 1742871, 4494159, 14356645383, 52461, 52461,
    110751, 167108032289, 568012283019, 41777007381, 11505, 11505,
    11187805119, 19080389907, 11187804699, 21215, 21215, 1001,
    156789938799, 3819, 5753019100785, 60099, 1809, 1472719112271159,
    1809, 1809, 154971, 1809, 60099, 154971,
    40192034253513, 1809, 1809, 3819, 210044815494723, 367642849444285,
    210044813487683, 123163386067153, 123163331512111, 13265696909, 5651522067, 13265696475,
    23541, 23541, 1047, 1005, 1005, 1001,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    990960272231297830222823424, 8230475594365501423239561216, 42446131660573923727877603328, 33104170392150605736355823616, 990960272231297830222823424, 990960272231297830222823424,
    1046013620688592154124091392, 1541299552148187573727120064512, 5238988607787485414855490404352, 1541299526645563891823664955392, 222539064874660938479912878080, 222539064874660938479912878080,
    51594644444182658722169880576, 175985534720509896351710969856, 51594642507274530982666960896, 205178890104994863531132190720, 205178890104994863531132190720, 38724311853895801724188229632,
    11297905759209908370212388864, 72138870392316700284420096, 414548714856810751551351029760, 567619006507965615395831808, 68342087740089505532608512, 414533577827862458467356770304,
    68342087740089505532608512, 68342087740089505532608512, 2927319424867167153646731264, 68342087740089505532608512, 567619006507965615395831808, 2927319424867167153646731264,
    11313051905461459885152534528, 68342087740089505532608512, 68342087740089505532608512, 72138870392316700284420096, 236489438198284771807463473152, 827858099881354644214702407680,
    236489435938558622778043400192, 138669644899429697409066729472, 138669583475912991813627019264, 61177228959930716759036788736, 208504362393742011012999020544, 61177226958458984761550438400,
    227674581756383883214064713728, 227674581756383883214064713728, 40503850660368535869355720704, 9719763589701618564637655040, 9719763589701618564637655040, 38724311853895801724188229632,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    15, 20, 22, 33, 15, 15,
    16, 37, 39, 35, 13, 13,
    33, 34, 33, 14, 14, 9,
    37, 11, 42, 15, 10, 50,
    10, 10, 17, 10, 15, 17,
    45, 10, 10, 11, 47, 48,
    47, 46, 46, 33, 32, 33,
    14, 14, 10, 9, 9, 9,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15318789922085690, 0, 0, 0, 0, 10682116764947138,
    14263195831184002, 14844264415704613, 13058837332677816, 10682116764947138, 15056595381891146, 14063310809257124,
    10682116764947138, 14263195831184002, 10682116764947138
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15678957687792584, 20733034360659112, 22099619736221536, 33740999633128957, 15678957687792584, 15678957687792584,
    16756960200011716, 37281990124048193, 39047131171482135, 35281990100177097, 13489973363111646, 13489973363111646,
    33381207977634033, 34151371601933388, 33381207923473997, 14372797058178101, 14372797058178101, 9967226272738856,
    37190042028529801, 11898979208910875, 42387456398816976, 15875053368150273, 10820976693606152, 50387403718602255,
    10820976693606152, 10820976693606152, 17241638741093964, 10820976693606152, 15875053368150273, 17241638741093964,
    45191974832409942, 10820976693606152, 10820976693606152, 11898979208910875, 47577690504860554, 48385298253586735,
    47577690491075179, 46807566765484066, 46807566126444253, 33626981417949731, 32395992320237886, 33626981370750578,
    14522887985584760, 14522887985584760, 10032045726930809, 9972979801353332, 9972979801353332, 9967226272738856,
    0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 597804578541 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2852588901 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 8230475594365501423239561216, coefficient := (-8230475594365501423239561216) }, { argument := 42446131660573923727877603328, coefficient := (-42446131660573923727877603328) }, { argument := 33104170392150605736355823616, coefficient := (-33104170392150605736355823616) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1541299552148187573727120064512, coefficient := (-1541299552148187573727120064512) }, { argument := 5238988607787485414855490404352, coefficient := (-5238988607787485414855490404352) }, { argument := 1541299526645563891823664955392, coefficient := (-1541299526645563891823664955392) }, { argument := 222539064874660938479912878080, coefficient := (-222539064874660938479912878080) }, { argument := 222539064874660938479912878080, coefficient := (-222539064874660938479912878080) }, { argument := 51594644444182658722169880576, coefficient := (-51594644444182658722169880576) }, { argument := 175985534720509896351710969856, coefficient := (-175985534720509896351710969856) }, { argument := 51594642507274530982666960896, coefficient := (-51594642507274530982666960896) }, { argument := 205178890104994863531132190720, coefficient := (-205178890104994863531132190720) }, { argument := 205178890104994863531132190720, coefficient := (-205178890104994863531132190720) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 11297905759209908370212388864, coefficient := (-11297905759209908370212388864) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 414548714856810751551351029760, coefficient := (-414548714856810751551351029760) }, { argument := 567619006507965615395831808, coefficient := (-567619006507965615395831808) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 414533577827862458467356770304, coefficient := (-414533577827862458467356770304) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 2927319424867167153646731264, coefficient := (-2927319424867167153646731264) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 567619006507965615395831808, coefficient := (-567619006507965615395831808) }, { argument := 2927319424867167153646731264, coefficient := (-2927319424867167153646731264) }, { argument := 11313051905461459885152534528, coefficient := (-11313051905461459885152534528) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 68342087740089505532608512, coefficient := (-68342087740089505532608512) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 236489438198284771807463473152, coefficient := (-236489438198284771807463473152) }, { argument := 827858099881354644214702407680, coefficient := (-827858099881354644214702407680) }, { argument := 236489435938558622778043400192, coefficient := (-236489435938558622778043400192) }, { argument := 138669644899429697409066729472, coefficient := (-138669644899429697409066729472) }, { argument := 138669583475912991813627019264, coefficient := (-138669583475912991813627019264) }, { argument := 61177228959930716759036788736, coefficient := (-61177228959930716759036788736) }, { argument := 208504362393742011012999020544, coefficient := (-208504362393742011012999020544) }, { argument := 61177226958458984761550438400, coefficient := (-61177226958458984761550438400) }, { argument := 227674581756383883214064713728, coefficient := (-227674581756383883214064713728) }, { argument := 227674581756383883214064713728, coefficient := (-227674581756383883214064713728) }, { argument := 40503850660368535869355720704, coefficient := (-40503850660368535869355720704) }, { argument := 9719763589701618564637655040, coefficient := (-9719763589701618564637655040) }, { argument := 9719763589701618564637655040, coefficient := (-9719763589701618564637655040) }, { argument := 38724311853895801724188229632, coefficient := (-38724311853895801724188229632) }, { argument := 3238134230120497741785734794182656, coefficient := 3238134230120497741785734794182656 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 760675468514638510791921238016, coefficient := 760675468514638510791921238016 }, { argument := 568968847743429074783714672640, coefficient := 568968847743429074783714672640 }, { argument := 660208897201384367857139187712, coefficient := 660208897201384367857139187712 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 659183728106351162316988350464, coefficient := 659183728106351162316988350464 }, { argument := 662259235391450778937440862208, coefficient := 662259235391450778937440862208 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }, { argument := 760675468514638510791921238016, coefficient := 760675468514638510791921238016 }, { argument := 31780241946029371744675954688, coefficient := 31780241946029371744675954688 }] }

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

end TermShard11


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
