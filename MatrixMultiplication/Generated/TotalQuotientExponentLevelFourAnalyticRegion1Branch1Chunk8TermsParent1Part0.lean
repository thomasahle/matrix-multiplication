import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1049706160799632331848604723445760)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25165821, 7980637409, 31865299937, 15865858653, 31865299937, 2319397188541,
    7955280863, 86827478234603, 6601493267, 81367157, 206051731, 834651363,
    291027360203, 7955280863, 81367157, 308119666013, 15631954215587, 5400525,
    437067, 93660699, 167675235, 1953815100941, 93660699, 2728875,
    2750763, 5400525, 5356749, 167675235, 5356749, 38514827763,
    437067, 25165827, 29245072111, 116767620079, 58135696947, 116767620079,
    363656536164855, 78254509201, 13602779238469889, 259774567711, 12806897599, 129733916393,
    262735526157, 45629690342561, 78254509201, 12806897599, 19246978162957, 1809015124918003,
    1863257427, 151027749, 32369275845, 58446281853, 1809004810679525, 32369275845,
    954234549, 955504053, 1863257427, 1860718419, 58446281853, 1860718419,
    19246892624667, 151027749, 13167, 39501
  ]
def negativeCoefficients : Array ℕ := #[
    118842229604297057781380284416, 73608387914447750513633001472, 73476379096229012308202881024, 73168358520385289828865933312, 73476379096229012308202881024, 2611409078509355913743171584,
    18343628764280032173884440576, 97759049655719480667272118272, 15222007100083219588326621184, 750479560592172329369337856, 15203934190807378806842589184, 15396600084033849722413252608,
    2621341421929699834253541376, 18343628764280032173884440576, 750479560592172329369337856, 346911903260417120232538112, 17600015795097566823776780288, 199244205077340552481996800,
    257998818946048403076808704, 3455469888435488254662279168, 6186124295088212777914859520, 17598401921097471257290473472, 3455469888435488254662279168, 201355434936576610664448000,
    202970484273718029327532032, 199244205077340552481996800, 197629155740199133818912768, 6186124295088212777914859520, 197629155740199133818912768, 346910727923371268055760896,
    257998818946048403076808704, 118842257938495954999251566592, 269738180324398868139698290688, 269247800461682711911316062208, 268103580782011680711757529088, 269247800461682711911316062208,
    102360215047680392533251194880, 721770451922298164567928209408, 3828841969348506965491721437184, 598999370927918736402255183872, 29530695298369791951789621248, 598292088345425799678915510272,
    605826876261200079328288702464, 102748928211894419788952240128, 721770451922298164567928209408, 29530695298369791951789621248, 43340341841350609419250958336, 4073539921244154792053250719744,
    17185516449653778744675926016, 22287761870651549282910339072, 298553873682011744334784757760, 539071801701092930503493812224, 4073516695643871726437348147200, 298553873682011744334784757760,
    17602520511694656743285981184, 17625938727083207313900699648, 17185516449653778744675926016, 17162098234265228174061207552, 539071801701092930503493812224, 17162098234265228174061207552,
    43340149226245124464538812416, 22287761870651549282910339072, 1989740783358227792919527424, 1492305587518670844689645568
  ]
def negativeScales : Array ℕ := #[
    24, 32, 34, 33, 34, 41,
    32, 46, 32, 26, 27, 29,
    38, 32, 26, 38, 43, 22,
    18, 26, 27, 40, 26, 21,
    21, 22, 22, 27, 22, 35,
    18, 24, 34, 36, 35, 36,
    48, 36, 53, 37, 33, 36,
    37, 45, 36, 33, 44, 50,
    30, 27, 34, 35, 50, 34,
    29, 29, 30, 30, 35, 30,
    44, 27, 13, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    24584962328742205, 32893856836183845, 34891267193006401, 33885206553578546, 34891267193006401, 41076887036196565,
    32889265723716670, 46303216917211005, 32620145255015792, 26277943247466539, 27618431342574390, 29636598463402469,
    38082363834604777, 32889265723716670, 26277943247466539, 38164699810377049, 43829563381619518, 22364668231800296,
    18737494928609320, 26480940469279091, 27321094383117268, 40829431084304898, 26480940469279091, 21379874880751789,
    21391400414738474, 22364668231800296, 22352926266923834, 27321094383117268, 22352926266923834, 35164694922519977,
    18737494928609320, 24584962672707506, 34767474495607992, 36764849311201203, 35758705240038656, 36764849311201203,
    48369569835172083, 36187454834650376, 53594750962613739, 37918469245682517, 33576201981885103, 36916764742920120,
    37934820341528181, 45375038096769915, 36187454834650376, 33576201981885103, 44129697189393477, 50684125893537532,
    30795179864868177, 27170238405779797, 34913906044866035, 35766392197683087, 50684117667877649, 34913906044866035,
    29829768681730331, 29831686753068293, 30795179864868177, 30793212604599784, 35766392197683087, 30793212604599784,
    44129690777688743, 27170238405779797, 13684639055631019, 15269601556301956
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
noncomputable def negativeCeiling : ℝ := 331571909 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 118842229604297057781380284416, coefficient := (-118842229604297057781380284416) }, { argument := 73608387914447750513633001472, coefficient := (-73608387914447750513633001472) }, { argument := 73476379096229012308202881024, coefficient := (-73476379096229012308202881024) }, { argument := 73168358520385289828865933312, coefficient := (-73168358520385289828865933312) }, { argument := 73476379096229012308202881024, coefficient := (-73476379096229012308202881024) }, { argument := 2611409078509355913743171584, coefficient := (-2611409078509355913743171584) }, { argument := 18343628764280032173884440576, coefficient := (-18343628764280032173884440576) }, { argument := 97759049655719480667272118272, coefficient := (-97759049655719480667272118272) }, { argument := 15222007100083219588326621184, coefficient := (-15222007100083219588326621184) }, { argument := 750479560592172329369337856, coefficient := (-750479560592172329369337856) }, { argument := 15203934190807378806842589184, coefficient := (-15203934190807378806842589184) }, { argument := 15396600084033849722413252608, coefficient := (-15396600084033849722413252608) }, { argument := 2621341421929699834253541376, coefficient := (-2621341421929699834253541376) }, { argument := 18343628764280032173884440576, coefficient := (-18343628764280032173884440576) }, { argument := 750479560592172329369337856, coefficient := (-750479560592172329369337856) }, { argument := 346911903260417120232538112, coefficient := (-346911903260417120232538112) }, { argument := 17600015795097566823776780288, coefficient := (-17600015795097566823776780288) }, { argument := 199244205077340552481996800, coefficient := (-199244205077340552481996800) }, { argument := 257998818946048403076808704, coefficient := (-257998818946048403076808704) }, { argument := 3455469888435488254662279168, coefficient := (-3455469888435488254662279168) }, { argument := 6186124295088212777914859520, coefficient := (-6186124295088212777914859520) }, { argument := 17598401921097471257290473472, coefficient := (-17598401921097471257290473472) }, { argument := 3455469888435488254662279168, coefficient := (-3455469888435488254662279168) }, { argument := 201355434936576610664448000, coefficient := (-201355434936576610664448000) }, { argument := 202970484273718029327532032, coefficient := (-202970484273718029327532032) }, { argument := 199244205077340552481996800, coefficient := (-199244205077340552481996800) }, { argument := 197629155740199133818912768, coefficient := (-197629155740199133818912768) }, { argument := 6186124295088212777914859520, coefficient := (-6186124295088212777914859520) }, { argument := 197629155740199133818912768, coefficient := (-197629155740199133818912768) }, { argument := 346910727923371268055760896, coefficient := (-346910727923371268055760896) }, { argument := 257998818946048403076808704, coefficient := (-257998818946048403076808704) }, { argument := 118842257938495954999251566592, coefficient := (-118842257938495954999251566592) }, { argument := 269738180324398868139698290688, coefficient := (-269738180324398868139698290688) }, { argument := 269247800461682711911316062208, coefficient := (-269247800461682711911316062208) }, { argument := 268103580782011680711757529088, coefficient := (-268103580782011680711757529088) }, { argument := 269247800461682711911316062208, coefficient := (-269247800461682711911316062208) }, { argument := 102360215047680392533251194880, coefficient := (-102360215047680392533251194880) }, { argument := 721770451922298164567928209408, coefficient := (-721770451922298164567928209408) }, { argument := 3828841969348506965491721437184, coefficient := (-3828841969348506965491721437184) }, { argument := 598999370927918736402255183872, coefficient := (-598999370927918736402255183872) }, { argument := 29530695298369791951789621248, coefficient := (-29530695298369791951789621248) }, { argument := 598292088345425799678915510272, coefficient := (-598292088345425799678915510272) }, { argument := 605826876261200079328288702464, coefficient := (-605826876261200079328288702464) }, { argument := 102748928211894419788952240128, coefficient := (-102748928211894419788952240128) }, { argument := 721770451922298164567928209408, coefficient := (-721770451922298164567928209408) }, { argument := 29530695298369791951789621248, coefficient := (-29530695298369791951789621248) }, { argument := 43340341841350609419250958336, coefficient := (-43340341841350609419250958336) }, { argument := 4073539921244154792053250719744, coefficient := (-4073539921244154792053250719744) }, { argument := 17185516449653778744675926016, coefficient := (-17185516449653778744675926016) }, { argument := 22287761870651549282910339072, coefficient := (-22287761870651549282910339072) }, { argument := 298553873682011744334784757760, coefficient := (-298553873682011744334784757760) }, { argument := 539071801701092930503493812224, coefficient := (-539071801701092930503493812224) }, { argument := 4073516695643871726437348147200, coefficient := (-4073516695643871726437348147200) }, { argument := 298553873682011744334784757760, coefficient := (-298553873682011744334784757760) }, { argument := 17602520511694656743285981184, coefficient := (-17602520511694656743285981184) }, { argument := 17625938727083207313900699648, coefficient := (-17625938727083207313900699648) }, { argument := 17185516449653778744675926016, coefficient := (-17185516449653778744675926016) }, { argument := 17162098234265228174061207552, coefficient := (-17162098234265228174061207552) }, { argument := 539071801701092930503493812224, coefficient := (-539071801701092930503493812224) }, { argument := 17162098234265228174061207552, coefficient := (-17162098234265228174061207552) }, { argument := 43340149226245124464538812416, coefficient := (-43340149226245124464538812416) }, { argument := 22287761870651549282910339072, coefficient := (-22287761870651549282910339072) }, { argument := 1989740783358227792919527424, coefficient := (-1989740783358227792919527424) }, { argument := 1492305587518670844689645568, coefficient := (-1492305587518670844689645568) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5918354447239849308432934182584320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    83391, 215061, 179949, 5034183, 153615, 179949,
    162393, 83391, 83391, 162393, 5034183, 162393,
    13167, 215061, 611209704255, 9610679637219, 12705, 374840870323635,
    495, 825, 25245, 825, 495, 404415,
    25905, 19221382117825, 25245, 825, 25905, 825,
    25245, 825, 611209704255, 498781187, 1991547395, 991600119,
    1991547395, 90914156115011, 156509008639, 3400695851622933, 259774551227, 12806896793,
    129733908151, 262735509699, 11407425360693, 156509008639, 12806896793, 93752435103815,
    9492613592144825, 67087554777, 5439520623, 1165870355823, 2108697347223, 18985227467251145,
    1165870355823, 34449774399, 34450066239, 67087554777, 67086971097, 2108697347223,
    67086971097, 187503989557815, 5439520623, 513
  ]
def negativeCoefficients : Array ℕ := #[
    1575211453491930336061292544, 2031193716344857538605350912, 27193124039229113169900208128, 47546514135664318301639540736, 1450852654532041099003822080, 27193124039229113169900208128,
    1533758520505300590375469056, 1575211453491930336061292544, 1575211453491930336061292544, 1533758520505300590375469056, 47546514135664318301639540736, 1533758520505300590375469056,
    1989740783358227792919527424, 2031193716344857538605350912, 344080474541006132934082560, 43282653232956702080184090624, 1919925317275482958080245760, 422033300978188749593892618240,
    1196836561418482882959114240, 62335237573879316820787200, 1907458269760707094716088320, 1994727602364138138265190400, 1196836561418482882959114240, 30556733458715641105549885440,
    1957326459819810548172718080, 43282704671691292620200345600, 1907458269760707094716088320, 62335237573879316820787200, 1957326459819810548172718080, 62335237573879316820787200,
    1907458269760707094716088320, 1994727602364138138265190400, 344080474541006132934082560, 73607111242960525186129985536, 73475130212455891014925680640, 73167174474611744615448969216,
    73475130212455891014925680640, 102360239900566659971221028864, 721770406898407566661340102656, 3828843142542358153422220296192, 598999332918402572523724079104, 29530693439860326525552295936,
    598292050335909635800384405504, 605826838311635833689313640448, 102748953207347481455892627456, 721770406898407566661340102656, 29530693439860326525552295936, 422223431798617842473228042240,
    42750931036355539365415564083200, 154693369187786208703313608704, 200682889632292276254629953536, 2688314009623946435262463082496, 4862325036641615983706999095296, 42750931673528181086514797608960,
    2688314009623946435262463082496, 158871542933846070055661469696, 158872888808293687904547373056, 154693369187786208703313608704, 154692023313338590854427705344, 4862325036641615983706999095296,
    154692023313338590854427705344, 422221448751528503525108613120, 200682889632292276254629953536, 1240357890924609533248536576
  ]
def negativeScales : Array ℕ := #[
    16, 17, 17, 22, 17, 17,
    17, 16, 16, 17, 22, 17,
    13, 17, 39, 43, 13, 48,
    8, 9, 14, 9, 8, 18,
    14, 44, 14, 9, 14, 9,
    14, 9, 39, 28, 30, 29,
    30, 46, 37, 51, 37, 33,
    36, 37, 43, 37, 33, 46,
    53, 35, 32, 40, 40, 54,
    40, 35, 35, 35, 35, 40,
    35, 47, 32, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16347604068303230, 17714386399076023, 17457228559477788, 22263326230875469, 17228959571804610, 17457228559477788,
    17309129920488594, 16347604068303230, 16347604068303230, 17309129920488594, 22263326230875469, 17309129920488594,
    13684639055631019, 17714386399076023, 39152876493171005, 43127775596138047, 13633108754954498, 48413271592515725,
    8951284725619456, 9688250309187948, 14623710056949224, 9688250309187948, 8951284725619456, 18625476983123928,
    14660942963165521, 44127777310690129, 14623710056949224, 9688250309187948, 14660942963165521, 9688250309187948,
    14623710056949224, 9688250309187948, 39152876493171005, 28893831813713193, 30891242671195684, 29885183206999148,
    30891242671195684, 46369570185455944, 37187454744655356, 51594751404669250, 37918469154136263, 33576201891089325,
    36916764651265644, 37934820251156394, 43375038447730382, 37187454744655356, 33576201891089325, 46413921396741717,
    53075726781083534, 35965326123305161, 32340832368459241, 40084544509167837, 40939489193189899, 54075726802585891,
    40084544509167837, 35003775484067062, 35003787705753407, 35965326123305161, 35965313571407934, 40939489193189899,
    35965313571407934, 47413914620853160, 32340832368459241, 9002815015607055
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
noncomputable def negativeCeiling : ℝ := 67983921403 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1575211453491930336061292544, coefficient := (-1575211453491930336061292544) }, { argument := 2031193716344857538605350912, coefficient := (-2031193716344857538605350912) }, { argument := 27193124039229113169900208128, coefficient := (-27193124039229113169900208128) }, { argument := 47546514135664318301639540736, coefficient := (-47546514135664318301639540736) }, { argument := 1450852654532041099003822080, coefficient := (-1450852654532041099003822080) }, { argument := 27193124039229113169900208128, coefficient := (-27193124039229113169900208128) }, { argument := 1533758520505300590375469056, coefficient := (-1533758520505300590375469056) }, { argument := 1575211453491930336061292544, coefficient := (-1575211453491930336061292544) }, { argument := 1575211453491930336061292544, coefficient := (-1575211453491930336061292544) }, { argument := 1533758520505300590375469056, coefficient := (-1533758520505300590375469056) }, { argument := 47546514135664318301639540736, coefficient := (-47546514135664318301639540736) }, { argument := 1533758520505300590375469056, coefficient := (-1533758520505300590375469056) }, { argument := 1989740783358227792919527424, coefficient := (-1989740783358227792919527424) }, { argument := 2031193716344857538605350912, coefficient := (-2031193716344857538605350912) }, { argument := 344080474541006132934082560, coefficient := (-344080474541006132934082560) }, { argument := 43282653232956702080184090624, coefficient := (-43282653232956702080184090624) }, { argument := 1919925317275482958080245760, coefficient := (-1919925317275482958080245760) }, { argument := 422033300978188749593892618240, coefficient := (-422033300978188749593892618240) }, { argument := 1196836561418482882959114240, coefficient := (-1196836561418482882959114240) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 1994727602364138138265190400, coefficient := (-1994727602364138138265190400) }, { argument := 1196836561418482882959114240, coefficient := (-1196836561418482882959114240) }, { argument := 30556733458715641105549885440, coefficient := (-30556733458715641105549885440) }, { argument := 1957326459819810548172718080, coefficient := (-1957326459819810548172718080) }, { argument := 43282704671691292620200345600, coefficient := (-43282704671691292620200345600) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1957326459819810548172718080, coefficient := (-1957326459819810548172718080) }, { argument := 62335237573879316820787200, coefficient := (-62335237573879316820787200) }, { argument := 1907458269760707094716088320, coefficient := (-1907458269760707094716088320) }, { argument := 1994727602364138138265190400, coefficient := (-1994727602364138138265190400) }, { argument := 344080474541006132934082560, coefficient := (-344080474541006132934082560) }, { argument := 73607111242960525186129985536, coefficient := (-73607111242960525186129985536) }, { argument := 73475130212455891014925680640, coefficient := (-73475130212455891014925680640) }, { argument := 73167174474611744615448969216, coefficient := (-73167174474611744615448969216) }, { argument := 73475130212455891014925680640, coefficient := (-73475130212455891014925680640) }, { argument := 102360239900566659971221028864, coefficient := (-102360239900566659971221028864) }, { argument := 721770406898407566661340102656, coefficient := (-721770406898407566661340102656) }, { argument := 3828843142542358153422220296192, coefficient := (-3828843142542358153422220296192) }, { argument := 598999332918402572523724079104, coefficient := (-598999332918402572523724079104) }, { argument := 29530693439860326525552295936, coefficient := (-29530693439860326525552295936) }, { argument := 598292050335909635800384405504, coefficient := (-598292050335909635800384405504) }, { argument := 605826838311635833689313640448, coefficient := (-605826838311635833689313640448) }, { argument := 102748953207347481455892627456, coefficient := (-102748953207347481455892627456) }, { argument := 721770406898407566661340102656, coefficient := (-721770406898407566661340102656) }, { argument := 29530693439860326525552295936, coefficient := (-29530693439860326525552295936) }, { argument := 422223431798617842473228042240, coefficient := (-422223431798617842473228042240) }, { argument := 42750931036355539365415564083200, coefficient := (-42750931036355539365415564083200) }, { argument := 154693369187786208703313608704, coefficient := (-154693369187786208703313608704) }, { argument := 200682889632292276254629953536, coefficient := (-200682889632292276254629953536) }, { argument := 2688314009623946435262463082496, coefficient := (-2688314009623946435262463082496) }, { argument := 4862325036641615983706999095296, coefficient := (-4862325036641615983706999095296) }, { argument := 42750931673528181086514797608960, coefficient := (-42750931673528181086514797608960) }, { argument := 2688314009623946435262463082496, coefficient := (-2688314009623946435262463082496) }, { argument := 158871542933846070055661469696, coefficient := (-158871542933846070055661469696) }, { argument := 158872888808293687904547373056, coefficient := (-158872888808293687904547373056) }, { argument := 154693369187786208703313608704, coefficient := (-154693369187786208703313608704) }, { argument := 154692023313338590854427705344, coefficient := (-154692023313338590854427705344) }, { argument := 4862325036641615983706999095296, coefficient := (-4862325036641615983706999095296) }, { argument := 154692023313338590854427705344, coefficient := (-154692023313338590854427705344) }, { argument := 422221448751528503525108613120, coefficient := (-422221448751528503525108613120) }, { argument := 200682889632292276254629953536, coefficient := (-200682889632292276254629953536) }, { argument := 1240357890924609533248536576, coefficient := (-1240357890924609533248536576) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
