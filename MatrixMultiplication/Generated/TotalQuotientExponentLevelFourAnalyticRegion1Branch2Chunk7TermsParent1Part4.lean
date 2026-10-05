import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-211738932774273956431516930146304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    73945, 4025, 133745, 73945, 3529236825, 4255,
    4025, 5405, 27101794615, 186037157449, 54203588425, 663,
    663, 38295, 29785, 4255, 39997, 472305,
    33189, 29785, 472305, 4255, 33189, 33189,
    33189, 33189, 33189, 38295, 39997, 1610385,
    257093445, 10261623855, 257093445, 6440805, 36225, 28175,
    4025, 37835, 446775, 31395, 28175, 446775,
    4025, 31395, 31395, 31395, 31395, 31395,
    36225, 37835, 966231, 154256067, 6156974313, 154256067,
    3864483, 1758615759, 42159, 64453147441, 1043211, 33189,
    128896550567, 17043, 17043, 576771
  ]
def negativeCoefficients : Array ℕ := #[
    2793563116606367322614005760, 152060200748402575881011200, 5052743242011205592846172160, 2793563116606367322614005760, 8137866060785782989678182400, 160749355076882723074211840,
    152060200748402575881011200, 204195126719283459040215040, 249969934600572344530286673920, 857944957915527878870246096896, 249969930888165099696239411200, 51297140377887945141132460032,
    51297140377887945141132460032, 180843024461493063458488320, 140655685692272382689935360, 160749355076882723074211840, 188880492215337199612198912, 2230397301691747782654689280,
    5015379878398740959915409408, 140655685692272382689935360, 2230397301691747782654689280, 160749355076882723074211840, 156730621199960654997356544, 156730621199960654997356544,
    156730621199960654997356544, 5015379878398740959915409408, 156730621199960654997356544, 180843024461493063458488320, 188880492215337199612198912, 29706359955140756279132160,
    4742536982943322554362757120, 47323387258464453301024849920, 4742536982943322554362757120, 29702970365917212149022720, 171067725841952897866137600, 133052675654852253895884800,
    152060200748402575881011200, 178670735879373026660188160, 2109835285384085740349030400, 4744278263350160367487549440, 133052675654852253895884800, 2109835285384085740349030400,
    152060200748402575881011200, 148258695729692511483985920, 148258695729692511483985920, 148258695729692511483985920, 4744278263350160367487549440, 148258695729692511483985920,
    171067725841952897866137600, 178670735879373026660188160, 570362111138702520559337472, 91056710072511793043764936704, 908609035362517503379677118464, 91056710072511793043764936704,
    570297031025610473261236224, 8110183707566368765180379136, 199090248551301372564209664, 297237678897298675529011953664, 4926424660960925453025017856, 156730621199960654997356544,
    297215210036676349392830070784, 160966583935094726754041856, 160966583935094726754041856, 2723724038691208139548655616
  ]
def negativeScales : Array ℕ := #[
    16, 11, 17, 16, 31, 12,
    11, 12, 34, 37, 35, 9,
    9, 15, 14, 12, 15, 18,
    15, 14, 18, 12, 15, 15,
    15, 15, 15, 15, 15, 20,
    27, 33, 27, 22, 15, 14,
    11, 15, 18, 14, 14, 18,
    11, 14, 14, 14, 14, 14,
    15, 15, 19, 27, 32, 27,
    21, 30, 15, 35, 19, 15,
    36, 14, 14, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16174164978272323, 11974773083633342, 17029125432417594, 16174164978272323, 31716709097695814, 12054943416573326,
    11974773083633342, 12400078902622020, 34657669335402531, 37436799845274765, 35657669313976468, 9372865060112590,
    9372865060112590, 15224868418015638, 14862298340817341, 12054943416573326, 15287604173363601, 18849359284634491,
    15018417540548212, 14862298340817341, 18849359284634491, 12054943416573326, 15018417540548212, 15018417540548212,
    15018417540548212, 15018417540548212, 15018417540548212, 15224868418015638, 15287604173363601, 20618974208723429,
    27937717594428827, 33256539997770140, 27937717594428827, 22618809583283499, 15144698069331655, 14782127990393705,
    11974773083633342, 15207433824679617, 18769188934579560, 14938247200400131, 14782127990393705, 18769188934579560,
    11974773083633342, 14938247200400131, 14938247200400131, 14938247200400131, 14938247200400131, 14938247200400131,
    15144698069331655, 15207433824679617, 19882008617699835, 27200751991803792, 32519574403604448, 27200751991803792,
    21881843992250449, 30711793156027240, 15363553026596901, 35907531765313753, 19992599577423370, 15018417540548212,
    36907422704638677, 14056891688362847, 14056891688362847, 19137639102247209
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
noncomputable def negativeCeiling : ℝ := 264883741 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 8137866060785782989678182400, coefficient := (-8137866060785782989678182400) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 249969934600572344530286673920, coefficient := (-249969934600572344530286673920) }, { argument := 857944957915527878870246096896, coefficient := (-857944957915527878870246096896) }, { argument := 249969930888165099696239411200, coefficient := (-249969930888165099696239411200) }, { argument := 51297140377887945141132460032, coefficient := (-51297140377887945141132460032) }, { argument := 51297140377887945141132460032, coefficient := (-51297140377887945141132460032) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 29706359955140756279132160, coefficient := (-29706359955140756279132160) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 47323387258464453301024849920, coefficient := (-47323387258464453301024849920) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 29702970365917212149022720, coefficient := (-29702970365917212149022720) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 570362111138702520559337472, coefficient := (-570362111138702520559337472) }, { argument := 91056710072511793043764936704, coefficient := (-91056710072511793043764936704) }, { argument := 908609035362517503379677118464, coefficient := (-908609035362517503379677118464) }, { argument := 91056710072511793043764936704, coefficient := (-91056710072511793043764936704) }, { argument := 570297031025610473261236224, coefficient := (-570297031025610473261236224) }, { argument := 8110183707566368765180379136, coefficient := (-8110183707566368765180379136) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 297237678897298675529011953664, coefficient := (-297237678897298675529011953664) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 297215210036676349392830070784, coefficient := (-297215210036676349392830070784) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }] }

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

end TermShard8


end Parent1

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-191904584741515785491006298783744)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31395, 1043211, 576771, 3526975833, 33189, 31395,
    42159, 1610385, 257093445, 10261623855, 257093445, 6440805,
    756841707, 42159, 27625205013, 1043211, 33189, 55246233891,
    17043, 17043, 576771, 31395, 1043211, 576771,
    1517859549, 33189, 31395, 42159, 430482675, 23637746235,
    6887722645, 48645, 37835, 5405, 50807, 599955,
    42159, 37835, 599955, 5405, 42159, 42159,
    42159, 42159, 42159, 48645, 50807, 24799929,
    3959239053, 158029007367, 3959239053, 99188397, 1758615759, 42159,
    64453147441, 1043211, 33189, 128896550567, 17043, 17043,
    576771, 31395, 1043211, 576771
  ]
def negativeCoefficients : Array ℕ := #[
    148258695729692511483985920, 4926424660960925453025017856, 2723724038691208139548655616, 8132652568188694901362262016, 156730621199960654997356544, 148258695729692511483985920,
    199090248551301372564209664, 29706359955140756279132160, 4742536982943322554362757120, 47323387258464453301024849920, 4742536982943322554362757120, 29702970365917212149022720,
    6980632636669235433629024256, 199090248551301372564209664, 254797543429284573404152725504, 4926424660960925453025017856, 156730621199960654997356544, 254778284405894008144568254464,
    160966583935094726754041856, 160966583935094726754041856, 2723724038691208139548655616, 148258695729692511483985920, 4926424660960925453025017856, 2723724038691208139548655616,
    6999891660059800693213495296, 156730621199960654997356544, 148258695729692511483985920, 199090248551301372564209664, 7941003733890884952706252800, 27252465954771032262165135360,
    7941003555188051738644971520, 229719517559193891420241920, 178670735879373026660188160, 204195126719283459040215040, 239929273895158064372252672, 2833207383230057994182983680,
    6370887953641643922054709248, 178670735879373026660188160, 2833207383230057994182983680, 204195126719283459040215040, 199090248551301372564209664, 199090248551301372564209664,
    199090248551301372564209664, 6370887953641643922054709248, 199090248551301372564209664, 229719517559193891420241920, 239929273895158064372252672, 914955886618335293397270528,
    146070139074654334674372919296, 1457560327560705161671565377536, 146070139074654334674372919296, 914851487270250134189899776, 8110183707566368765180379136, 199090248551301372564209664,
    297237678897298675529011953664, 4926424660960925453025017856, 156730621199960654997356544, 297215210036676349392830070784, 160966583935094726754041856, 160966583935094726754041856,
    2723724038691208139548655616, 148258695729692511483985920, 4926424660960925453025017856, 2723724038691208139548655616
  ]
def negativeScales : Array ℕ := #[
    14, 19, 19, 31, 15, 14,
    15, 20, 27, 33, 27, 22,
    29, 15, 34, 19, 15, 35,
    14, 14, 19, 14, 19, 19,
    30, 15, 14, 15, 28, 34,
    32, 15, 15, 12, 15, 19,
    15, 15, 19, 12, 15, 15,
    15, 15, 15, 15, 15, 24,
    31, 37, 31, 26, 30, 15,
    35, 19, 15, 36, 14, 14,
    19, 14, 19, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14938247200400131, 19992599577423370, 19137639102247209, 31715784544476252, 15018417540548212, 14938247200400131,
    15363553026596901, 20618974208723429, 27937717594428827, 33256539997770140, 27937717594428827, 22618809583283499,
    29495416352036672, 15363553026596901, 34685266120040113, 19992599577423370, 15018417540548212, 35685157068958537,
    14056891688362847, 14056891688362847, 19137639102247209, 14938247200400131, 19992599577423370, 19137639102247209,
    30499391155058937, 15018417540548212, 14938247200400131, 15363553026596901, 28681379935920657, 34460373435717713,
    32681379903454523, 15570003904066736, 15207433824679617, 12400078902622020, 15632739659425936, 19194494768972119,
    15363553026596901, 15207433824679617, 19194494768972119, 12400078902622020, 15363553026596901, 15363553026596901,
    15363553026596901, 15363553026596901, 15363553026596901, 15570003904066736, 15632739659425936, 24563832654523500,
    31882576034962574, 37201398443577679, 31882576034962574, 26563668029083603, 30711793156027240, 15363553026596901,
    35907531765313753, 19992599577423370, 15018417540548212, 36907422704638677, 14056891688362847, 14056891688362847,
    19137639102247209, 14938247200400131, 19992599577423370, 19137639102247209
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
noncomputable def negativeCeiling : ℝ := 652926129 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 8132652568188694901362262016, coefficient := (-8132652568188694901362262016) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 29706359955140756279132160, coefficient := (-29706359955140756279132160) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 47323387258464453301024849920, coefficient := (-47323387258464453301024849920) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 29702970365917212149022720, coefficient := (-29702970365917212149022720) }, { argument := 6980632636669235433629024256, coefficient := (-6980632636669235433629024256) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 254797543429284573404152725504, coefficient := (-254797543429284573404152725504) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 254778284405894008144568254464, coefficient := (-254778284405894008144568254464) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 6999891660059800693213495296, coefficient := (-6999891660059800693213495296) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 7941003733890884952706252800, coefficient := (-7941003733890884952706252800) }, { argument := 27252465954771032262165135360, coefficient := (-27252465954771032262165135360) }, { argument := 7941003555188051738644971520, coefficient := (-7941003555188051738644971520) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 914955886618335293397270528, coefficient := (-914955886618335293397270528) }, { argument := 146070139074654334674372919296, coefficient := (-146070139074654334674372919296) }, { argument := 1457560327560705161671565377536, coefficient := (-1457560327560705161671565377536) }, { argument := 146070139074654334674372919296, coefficient := (-146070139074654334674372919296) }, { argument := 914851487270250134189899776, coefficient := (-914851487270250134189899776) }, { argument := 8110183707566368765180379136, coefficient := (-8110183707566368765180379136) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 297237678897298675529011953664, coefficient := (-297237678897298675529011953664) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 297215210036676349392830070784, coefficient := (-297215210036676349392830070784) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }] }

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

end TermShard9


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
