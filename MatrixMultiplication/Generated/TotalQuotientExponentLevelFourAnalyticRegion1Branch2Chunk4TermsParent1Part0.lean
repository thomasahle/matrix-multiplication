import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

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
def constantNumerator : ℤ := (-288545973525419010147172229316608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    535, 489, 535, 489, 6753471410745, 4288676733,
    53704551267783, 6908108031, 214005825, 6908108031, 4613965587, 6823596839481,
    4288676733, 25680699, 37796440609281, 1055197974392319, 389270525, 344782465,
    16138043765, 4393195925, 527599150283487, 16138043765, 389270525, 389270525,
    166830225, 389270525, 4393195925, 166830225, 18898057217313, 344782465,
    108888237, 9156329299, 4578163545, 54445223, 402369974963, 38635964661593,
    313739199, 382256131667555, 321941531, 10252915, 313739199, 178400721,
    321941531, 5025978933, 6151749, 19317990351471, 313739199, 10252915,
    6151749, 10252915, 157894891, 178400721, 402369974963, 535,
    489, 535, 489, 184313145066707, 7268727939, 1462035145751341,
    11708310273, 362710975, 11708310273, 7820048621
  ]
def negativeCoefficients : Array ℕ := #[
    10348405015901225735484866560, 9458635612664858662901121024, 10348405015901225735484866560, 9458635612664858662901121024, 15207465664444239967955189760, 79112122108523791015401750528,
    241863797077687217343449530368, 127432100881394609479898628096, 3947710684058073403962163200, 127432100881394609479898628096, 85112642348292062589424238592, 15365374091806562904113676288,
    79112122108523791015401750528, 3789802256695750467803676672, 10638752240243062149885198336, 297011825267209376799091851264, 7180773750113555855074918400, 6360113892957720900209213440,
    297694363183279129877534474240, 81040160894138701792988364800, 297011917077212796530347474944, 297694363183279129877534474240, 7180773750113555855074918400, 7180773750113555855074918400,
    6154948928668762161492787200, 7180773750113555855074918400, 81040160894138701792988364800, 6154948928668762161492787200, 10638660430239642418629574656, 6360113892957720900209213440,
    251079180072053890690842624, 21113057904157672884716699648, 21113052810550465531666759680, 251084273679261243740782592, 226514158663555325630611456, 21750114506631235798634070016,
    1446866677460907920663248896, 215191071517260994220035932160, 1484693257263807474144641024, 47283224753624441851740160, 1446866677460907920663248896, 822728110713065288220278784,
    1484693257263807474144641024, 23178236774226701395723026432, 907837915269589283553411072, 21750123537107908163643899904, 1446866677460907920663248896, 47283224753624441851740160,
    907837915269589283553411072, 47283224753624441851740160, 1456323322411632809033596928, 822728110713065288220278784, 226514158663555325630611456, 10348405015901225735484866560,
    9458635612664858662901121024, 10348405015901225735484866560, 9458635612664858662901121024, 51879538215119113644557729792, 268168728064310586404763598848, 823052617201038516963761979392,
    431960406283230824807673102336, 13381673057101326666904371200, 431960406283230824807673102336, 288508871111104602938458243072
  ]
def negativeScales : Array ℕ := #[
    9, 8, 9, 8, 42, 31,
    45, 32, 27, 32, 32, 42,
    31, 24, 45, 49, 28, 28,
    33, 32, 48, 33, 28, 28,
    27, 28, 32, 27, 44, 28,
    26, 33, 32, 25, 38, 45,
    28, 48, 28, 23, 28, 27,
    28, 32, 22, 44, 28, 23,
    22, 23, 27, 27, 38, 9,
    8, 9, 8, 47, 32, 50,
    33, 28, 33, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9063395081288510, 8933690662845865, 9063395081288510, 8933690662845865, 42618766403739043, 31997885451121588,
    45610109590156582, 32685643498365071, 27673074824848482, 32685643498365071, 32103360097788348, 42633669548673805,
    31997885451121588, 24614181135765331, 45103315611973461, 49906435128449409, 28536197869142798, 28361111162583838,
    33909746661459866, 32032623695261426, 48906435574404137, 33909746661459866, 28536197869142798, 28536197869142798,
    27313805447805480, 28536197869142798, 32032623695261426, 27313805447805480, 44103303161790849, 28361111162583838,
    26698272869895627, 33092122203019146, 32092121854963323, 25698302137345560, 38549731698338875, 45135009653104716,
    28224990551812153, 48441532972077008, 28262223458011129, 23289530804006864, 28224990551812153, 27410546204968240,
    28262223458011129, 32226757477986341, 22552565209842095, 44135010252100238, 28224990551812153, 23289530804006864,
    22552565209842095, 23289530804006864, 27234389249814403, 27410546204968240, 38549731698338875, 9063395081288510,
    8933690662845865, 9063395081288510, 8933690662845865, 47389152294922220, 32759055762191544, 50376899415853676,
    33446813832000410, 28434245158497339, 33446813832000410, 32864530433755024
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
noncomputable def negativeCeiling : ℝ := 1160918129 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 15207465664444239967955189760, coefficient := (-15207465664444239967955189760) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 241863797077687217343449530368, coefficient := (-241863797077687217343449530368) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 3947710684058073403962163200, coefficient := (-3947710684058073403962163200) }, { argument := 127432100881394609479898628096, coefficient := (-127432100881394609479898628096) }, { argument := 85112642348292062589424238592, coefficient := (-85112642348292062589424238592) }, { argument := 15365374091806562904113676288, coefficient := (-15365374091806562904113676288) }, { argument := 79112122108523791015401750528, coefficient := (-79112122108523791015401750528) }, { argument := 3789802256695750467803676672, coefficient := (-3789802256695750467803676672) }, { argument := 10638752240243062149885198336, coefficient := (-10638752240243062149885198336) }, { argument := 297011825267209376799091851264, coefficient := (-297011825267209376799091851264) }, { argument := 7180773750113555855074918400, coefficient := (-7180773750113555855074918400) }, { argument := 6360113892957720900209213440, coefficient := (-6360113892957720900209213440) }, { argument := 297694363183279129877534474240, coefficient := (-297694363183279129877534474240) }, { argument := 81040160894138701792988364800, coefficient := (-81040160894138701792988364800) }, { argument := 297011917077212796530347474944, coefficient := (-297011917077212796530347474944) }, { argument := 297694363183279129877534474240, coefficient := (-297694363183279129877534474240) }, { argument := 7180773750113555855074918400, coefficient := (-7180773750113555855074918400) }, { argument := 7180773750113555855074918400, coefficient := (-7180773750113555855074918400) }, { argument := 6154948928668762161492787200, coefficient := (-6154948928668762161492787200) }, { argument := 7180773750113555855074918400, coefficient := (-7180773750113555855074918400) }, { argument := 81040160894138701792988364800, coefficient := (-81040160894138701792988364800) }, { argument := 6154948928668762161492787200, coefficient := (-6154948928668762161492787200) }, { argument := 10638660430239642418629574656, coefficient := (-10638660430239642418629574656) }, { argument := 6360113892957720900209213440, coefficient := (-6360113892957720900209213440) }, { argument := 251079180072053890690842624, coefficient := (-251079180072053890690842624) }, { argument := 21113057904157672884716699648, coefficient := (-21113057904157672884716699648) }, { argument := 21113052810550465531666759680, coefficient := (-21113052810550465531666759680) }, { argument := 251084273679261243740782592, coefficient := (-251084273679261243740782592) }, { argument := 226514158663555325630611456, coefficient := (-226514158663555325630611456) }, { argument := 21750114506631235798634070016, coefficient := (-21750114506631235798634070016) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 215191071517260994220035932160, coefficient := (-215191071517260994220035932160) }, { argument := 1484693257263807474144641024, coefficient := (-1484693257263807474144641024) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 822728110713065288220278784, coefficient := (-822728110713065288220278784) }, { argument := 1484693257263807474144641024, coefficient := (-1484693257263807474144641024) }, { argument := 23178236774226701395723026432, coefficient := (-23178236774226701395723026432) }, { argument := 907837915269589283553411072, coefficient := (-907837915269589283553411072) }, { argument := 21750123537107908163643899904, coefficient := (-21750123537107908163643899904) }, { argument := 1446866677460907920663248896, coefficient := (-1446866677460907920663248896) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 907837915269589283553411072, coefficient := (-907837915269589283553411072) }, { argument := 47283224753624441851740160, coefficient := (-47283224753624441851740160) }, { argument := 1456323322411632809033596928, coefficient := (-1456323322411632809033596928) }, { argument := 822728110713065288220278784, coefficient := (-822728110713065288220278784) }, { argument := 226514158663555325630611456, coefficient := (-226514158663555325630611456) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 10348405015901225735484866560, coefficient := (-10348405015901225735484866560) }, { argument := 9458635612664858662901121024, coefficient := (-9458635612664858662901121024) }, { argument := 51879538215119113644557729792, coefficient := (-51879538215119113644557729792) }, { argument := 268168728064310586404763598848, coefficient := (-268168728064310586404763598848) }, { argument := 823052617201038516963761979392, coefficient := (-823052617201038516963761979392) }, { argument := 431960406283230824807673102336, coefficient := (-431960406283230824807673102336) }, { argument := 13381673057101326666904371200, coefficient := (-13381673057101326666904371200) }, { argument := 431960406283230824807673102336, coefficient := (-431960406283230824807673102336) }, { argument := 288508871111104602938458243072, coefficient := (-288508871111104602938458243072) }] }

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
def constantNumerator : ℤ := (-4446540394761296637644850665095168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    186214795183315, 7268727939, 43525317, 661653479506947, 17169995124915197, 14107292675,
    12495030655, 584848047755, 159210874475, 8585000574419613, 584848047755, 14107292675,
    14107292675, 6045982575, 14107292675, 159210874475, 6045982575, 330823727791459,
    12495030655, 2694404673, 226570446271, 113285195805, 1347229667, 38608796614489,
    2999654256460747, 23168818917, 27925091220774505, 23774539673, 757150945, 23168818917,
    13174426443, 23774539673, 371155393239, 454290567, 1499827969183629, 23168818917,
    757150945, 454290567, 757150945, 11660124553, 13174426443, 38608796614489,
    85720527, 7208174129, 3604086195, 42861133, 157218975, 11610209925,
    121011276375, 11610209925, 157218975, 9485326392583, 113521779, 165901323848981,
    2809060191, 89368209, 165901390889651, 45891783, 45891783, 1553074551,
    84537495, 2809060191, 1553074551, 9485216666473
  ]
def negativeCoefficients : Array ℕ := #[
    52414805137403166711233904640, 268168728064310586404763598848, 12846406134817273600228196352, 372477795469484827581521854464, 9665847955815164266204012478464, 260233617548642417589931212800,
    230492632685940427008224788480, 10788542258945147083514005422080, 2936922255191821569943509401600, 9665851346982915805276129984512, 10788542258945147083514005422080, 260233617548642417589931212800,
    260233617548642417589931212800, 223057386470264929362798182400, 260233617548642417589931212800, 2936922255191821569943509401600, 223057386470264929362798182400, 372474404301733288509404348416,
    230492632685940427008224788480, 6212874179229759039860637696, 522435879628412203509053652992, 522435753588727476879328542720, 6213000218914485669585747968, 21734820255779490988260589568,
    1688655223954617804092881240064, 213694636526009750922184359936, 15720428802020896245755213250560, 219281424409042685586816630784, 6983484853791168330790338560, 213694636526009750922184359936,
    121512636455966328955751890944, 219281424409042685586816630784, 3423304275328430715753423962112, 134082909192790431951174500352, 1688656170783809830544260202496, 213694636526009750922184359936,
    6983484853791168330790338560, 134082909192790431951174500352, 6983484853791168330790338560, 215091333496767984588342427648, 121512636455966328955751890944, 21734820255779490988260589568,
    197658077929063701182152704, 16620917924549657377330167808, 16620913914688664354716385280, 197662087790056723795935232, 1450089097677970076388556800, 214170571128517567739382988800,
    2232264045322559922081103872000, 214170571128517567739382988800, 1450089097677970076388556800, 10679528101781082463421857792, 261763400500651928592580608, 373576570133271406405419532288,
    6477251803877833892620664832, 206069059968598326764371968, 373576721095439621739614568448, 211638494021803686947192832, 211638494021803686947192832, 3581146096211046597553815552,
    194930191862187606398730240, 6477251803877833892620664832, 3581146096211046597553815552, 10679404561164055259908145152
  ]
def negativeScales : Array ℕ := #[
    47, 32, 25, 49, 53, 33,
    33, 39, 37, 52, 39, 33,
    33, 32, 33, 37, 32, 48,
    33, 31, 37, 36, 30, 45,
    51, 34, 54, 34, 29, 34,
    33, 34, 38, 28, 50, 34,
    29, 28, 29, 33, 33, 45,
    26, 32, 31, 25, 27, 33,
    36, 33, 27, 43, 26, 47,
    31, 26, 47, 25, 25, 30,
    26, 31, 30, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47403961031231837, 32759055762191544, 25375351469443747, 49233069176446903, 53930739155414744, 33715722096437428,
    33540635389776008, 39089270883454879, 37212147922452600, 52930739661570096, 39089270883454879, 33715722096437428,
    33715722096437428, 32493329674996869, 33715722096437428, 37212147922452600, 32493329674996869, 48233056041588319,
    33540635389776008, 31327319399621706, 37721168732932902, 36721168384877078, 30327348667071592, 45133994821605563,
    51413717646953382, 34431465450304806, 54632411511669930, 34468698356503850, 29496005702499731, 34431465450304806,
    33617021103469855, 34468698356503850, 38433232376478996, 28759040108606943, 50413718455872442, 34431465450304806,
    29496005702499731, 28759040108606943, 29496005702499731, 33440864148307066, 33617021103469855, 45133994821605563,
    26353137383777438, 32746986717180977, 31746986369125152, 25353166651227324, 27228200108288044, 33434675006780699,
    36816350535235970, 33434675006780699, 27228200108288044, 43108834556656122, 26758393862533560, 47237318727090204,
    31387440392059281, 26413258376215019, 47237319310082674, 25451732524029694, 25451732524029694, 30532479937914781,
    26333088027531025, 31387440392059281, 30532479937914781, 43108817867485521
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
noncomputable def negativeCeiling : ℝ := 43416350461 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 52414805137403166711233904640, coefficient := (-52414805137403166711233904640) }, { argument := 268168728064310586404763598848, coefficient := (-268168728064310586404763598848) }, { argument := 12846406134817273600228196352, coefficient := (-12846406134817273600228196352) }, { argument := 372477795469484827581521854464, coefficient := (-372477795469484827581521854464) }, { argument := 9665847955815164266204012478464, coefficient := (-9665847955815164266204012478464) }, { argument := 260233617548642417589931212800, coefficient := (-260233617548642417589931212800) }, { argument := 230492632685940427008224788480, coefficient := (-230492632685940427008224788480) }, { argument := 10788542258945147083514005422080, coefficient := (-10788542258945147083514005422080) }, { argument := 2936922255191821569943509401600, coefficient := (-2936922255191821569943509401600) }, { argument := 9665851346982915805276129984512, coefficient := (-9665851346982915805276129984512) }, { argument := 10788542258945147083514005422080, coefficient := (-10788542258945147083514005422080) }, { argument := 260233617548642417589931212800, coefficient := (-260233617548642417589931212800) }, { argument := 260233617548642417589931212800, coefficient := (-260233617548642417589931212800) }, { argument := 223057386470264929362798182400, coefficient := (-223057386470264929362798182400) }, { argument := 260233617548642417589931212800, coefficient := (-260233617548642417589931212800) }, { argument := 2936922255191821569943509401600, coefficient := (-2936922255191821569943509401600) }, { argument := 223057386470264929362798182400, coefficient := (-223057386470264929362798182400) }, { argument := 372474404301733288509404348416, coefficient := (-372474404301733288509404348416) }, { argument := 230492632685940427008224788480, coefficient := (-230492632685940427008224788480) }, { argument := 6212874179229759039860637696, coefficient := (-6212874179229759039860637696) }, { argument := 522435879628412203509053652992, coefficient := (-522435879628412203509053652992) }, { argument := 522435753588727476879328542720, coefficient := (-522435753588727476879328542720) }, { argument := 6213000218914485669585747968, coefficient := (-6213000218914485669585747968) }, { argument := 21734820255779490988260589568, coefficient := (-21734820255779490988260589568) }, { argument := 1688655223954617804092881240064, coefficient := (-1688655223954617804092881240064) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 15720428802020896245755213250560, coefficient := (-15720428802020896245755213250560) }, { argument := 219281424409042685586816630784, coefficient := (-219281424409042685586816630784) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 121512636455966328955751890944, coefficient := (-121512636455966328955751890944) }, { argument := 219281424409042685586816630784, coefficient := (-219281424409042685586816630784) }, { argument := 3423304275328430715753423962112, coefficient := (-3423304275328430715753423962112) }, { argument := 134082909192790431951174500352, coefficient := (-134082909192790431951174500352) }, { argument := 1688656170783809830544260202496, coefficient := (-1688656170783809830544260202496) }, { argument := 213694636526009750922184359936, coefficient := (-213694636526009750922184359936) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 134082909192790431951174500352, coefficient := (-134082909192790431951174500352) }, { argument := 6983484853791168330790338560, coefficient := (-6983484853791168330790338560) }, { argument := 215091333496767984588342427648, coefficient := (-215091333496767984588342427648) }, { argument := 121512636455966328955751890944, coefficient := (-121512636455966328955751890944) }, { argument := 21734820255779490988260589568, coefficient := (-21734820255779490988260589568) }, { argument := 197658077929063701182152704, coefficient := (-197658077929063701182152704) }, { argument := 16620917924549657377330167808, coefficient := (-16620917924549657377330167808) }, { argument := 16620913914688664354716385280, coefficient := (-16620913914688664354716385280) }, { argument := 197662087790056723795935232, coefficient := (-197662087790056723795935232) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 2232264045322559922081103872000, coefficient := (-2232264045322559922081103872000) }, { argument := 214170571128517567739382988800, coefficient := (-214170571128517567739382988800) }, { argument := 1450089097677970076388556800, coefficient := (-1450089097677970076388556800) }, { argument := 10679528101781082463421857792, coefficient := (-10679528101781082463421857792) }, { argument := 261763400500651928592580608, coefficient := (-261763400500651928592580608) }, { argument := 373576570133271406405419532288, coefficient := (-373576570133271406405419532288) }, { argument := 6477251803877833892620664832, coefficient := (-6477251803877833892620664832) }, { argument := 206069059968598326764371968, coefficient := (-206069059968598326764371968) }, { argument := 373576721095439621739614568448, coefficient := (-373576721095439621739614568448) }, { argument := 211638494021803686947192832, coefficient := (-211638494021803686947192832) }, { argument := 211638494021803686947192832, coefficient := (-211638494021803686947192832) }, { argument := 3581146096211046597553815552, coefficient := (-3581146096211046597553815552) }, { argument := 194930191862187606398730240, coefficient := (-194930191862187606398730240) }, { argument := 6477251803877833892620664832, coefficient := (-6477251803877833892620664832) }, { argument := 3581146096211046597553815552, coefficient := (-3581146096211046597553815552) }, { argument := 10679404561164055259908145152, coefficient := (-10679404561164055259908145152) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
