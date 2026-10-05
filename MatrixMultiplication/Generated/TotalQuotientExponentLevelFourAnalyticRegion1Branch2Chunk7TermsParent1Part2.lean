import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-192984700536040308472470000631808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    64454018865, 133745, 4255, 128898293415, 2185, 2185,
    73945, 4025, 133745, 73945, 3529236825, 4255,
    4025, 5405, 8702267503839, 14767742775777, 8702267483999, 19665,
    15295, 2185, 20539, 242535, 17043, 15295,
    242535, 2185, 17043, 17043, 17043, 17043,
    17043, 19665, 20539, 665505, 517615, 73945,
    695083, 8207895, 576771, 517615, 8207895, 73945,
    576771, 576771, 576771, 576771, 576771, 665505,
    695083, 49277781, 7867059417, 314005689963, 7867059417, 197088633,
    36225, 28175, 4025, 37835, 446775, 31395,
    28175, 446775, 4025, 31395
  ]
def negativeCoefficients : Array ℕ := #[
    297241697631175597597088808960, 5052743242011205592846172160, 160749355076882723074211840, 297219228770553271460906926080, 165093932241122796670812160, 165093932241122796670812160,
    2793563116606367322614005760, 152060200748402575881011200, 5052743242011205592846172160, 2793563116606367322614005760, 8137866060785782989678182400, 160749355076882723074211840,
    152060200748402575881011200, 204195126719283459040215040, 78383057375135393538310668288, 266032003448370525850533101568, 78383057196432560324249387008, 185730673771263146254663680,
    144457190710982447086960640, 165093932241122796670812160, 193985370383319286088204288, 2290678309845578803807518720, 5150930685923031256129339392, 144457190710982447086960640,
    2290678309845578803807518720, 165093932241122796670812160, 160966583935094726754041856, 160966583935094726754041856, 160966583935094726754041856, 5150930685923031256129339392,
    160966583935094726754041856, 185730673771263146254663680, 193985370383319286088204288, 3142758506182163237940756480, 2444367727030571407287255040, 2793563116606367322614005760,
    3282436662012481604071456768, 38760688242913346601269329920, 87159169238118660465556979712, 2444367727030571407287255040, 38760688242913346601269329920, 2793563116606367322614005760,
    2723724038691208139548655616, 2723724038691208139548655616, 2723724038691208139548655616, 87159169238118660465556979712, 2723724038691208139548655616, 3142758506182163237940756480,
    3282436662012481604071456768, 909014614627307142141444096, 145121631678065670163500367872, 1448095650109012271011360407552, 145121631678065670163500367872, 908910893197066691760095232,
    171067725841952897866137600, 133052675654852253895884800, 152060200748402575881011200, 178670735879373026660188160, 2109835285384085740349030400, 4744278263350160367487549440,
    133052675654852253895884800, 2109835285384085740349030400, 152060200748402575881011200, 148258695729692511483985920
  ]
def negativeScales : Array ℕ := #[
    35, 17, 12, 36, 11, 11,
    16, 11, 17, 16, 31, 12,
    11, 12, 42, 43, 42, 14,
    13, 11, 14, 17, 14, 13,
    17, 11, 14, 14, 14, 14,
    14, 14, 14, 19, 18, 16,
    19, 22, 19, 18, 22, 16,
    19, 19, 19, 19, 19, 19,
    19, 25, 32, 38, 32, 27,
    15, 14, 11, 15, 18, 14,
    14, 18, 11, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35907551270811095, 17029125432417594, 12054943416573326, 36907442211610582, 11093417564387961, 11093417564387961,
    16174164978272323, 11974773083633342, 17029125432417594, 16174164978272323, 31716709097695814, 12054943416573326,
    11974773083633342, 12400078902622020, 42984528522473868, 43747514563232955, 42984528519184716, 14263342565830274,
    13900772490874059, 11093417564387961, 14326078321178237, 17887833434243992, 14056891688362847, 13900772490874059,
    17887833434243992, 11093417564387961, 14056891688362847, 14056891688362847, 14056891688362847, 14056891688362847,
    14056891688362847, 14263342565830274, 14326078321178237, 19344089979714636, 18981519917909408, 16174164978272323,
    19406825735062607, 22968580858840259, 19137639102247209, 18981519917909408, 22968580858840259, 16174164978272323,
    19137639102247209, 19137639102247209, 19137639102247209, 19137639102247209, 19137639102247209, 19344089979714636,
    19406825735062607, 25554433956520759, 32873177336453864, 38191999745575429, 32873177336453864, 27554269331080864,
    15144698069331655, 14782127990393705, 11974773083633342, 15207433824679617, 18769188934579560, 14938247200400131,
    14782127990393705, 18769188934579560, 11974773083633342, 14938247200400131
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
noncomputable def negativeCeiling : ℝ := 671823257 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 297241697631175597597088808960, coefficient := (-297241697631175597597088808960) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 297219228770553271460906926080, coefficient := (-297219228770553271460906926080) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 8137866060785782989678182400, coefficient := (-8137866060785782989678182400) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 78383057375135393538310668288, coefficient := (-78383057375135393538310668288) }, { argument := 266032003448370525850533101568, coefficient := (-266032003448370525850533101568) }, { argument := 78383057196432560324249387008, coefficient := (-78383057196432560324249387008) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 909014614627307142141444096, coefficient := (-909014614627307142141444096) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 1448095650109012271011360407552, coefficient := (-1448095650109012271011360407552) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 908910893197066691760095232, coefficient := (-908910893197066691760095232) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 152060200748402575881011200, coefficient := (-152060200748402575881011200) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-268477967674734335673888409649152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    31395, 31395, 31395, 31395, 36225, 37835,
    28020699, 4473425943, 178552255077, 4473425943, 112070007, 1571713851,
    50807, 57097928901, 1257203, 39997, 114187227123, 20539,
    20539, 695083, 37835, 1257203, 695083, 3152058381,
    39997, 37835, 50807, 1203705, 936215, 133745,
    1257203, 14845695, 1043211, 936215, 14845695, 133745,
    1043211, 1043211, 1043211, 1043211, 1043211, 1203705,
    1257203, 50566089, 8072734173, 322214989047, 8072734173, 202241277,
    665505, 517615, 73945, 695083, 8207895, 576771,
    517615, 8207895, 73945, 576771, 576771, 576771,
    576771, 576771, 665505, 695083
  ]
def negativeCoefficients : Array ℕ := #[
    148258695729692511483985920, 148258695729692511483985920, 4744278263350160367487549440, 148258695729692511483985920, 171067725841952897866137600, 178670735879373026660188160,
    516890663219449159256899584, 82520143503213812445911973888, 823426938297281487437832388608, 82520143503213812445911973888, 516831684366959491392995328, 7248250791625366806466658304,
    239929273895158064372252672, 263317720393902770373739413504, 5936973309363166571594252288, 188880492215337199612198912, 263297819403065852938835460096, 193985370383319286088204288,
    193985370383319286088204288, 3282436662012481604071456768, 178670735879373026660188160, 5936973309363166571594252288, 3282436662012481604071456768, 7268151782462284241370611712,
    188880492215337199612198912, 178670735879373026660188160, 239929273895158064372252672, 5684336147262606291951943680, 4421150336759804893740400640, 5052743242011205592846172160,
    5936973309363166571594252288, 70106812482905477600740638720, 157645589150749614496800571392, 4421150336759804893740400640, 70106812482905477600740638720, 5052743242011205592846172160,
    4926424660960925453025017856, 4926424660960925453025017856, 4926424660960925453025017856, 157645589150749614496800571392, 4926424660960925453025017856, 5684336147262606291951943680,
    5936973309363166571594252288, 932779702591419747164749824, 148915661264420328206990573568, 1485954359915783833652180287488, 148915661264420328206990573568, 932673269489800461479313408,
    3142758506182163237940756480, 2444367727030571407287255040, 2793563116606367322614005760, 3282436662012481604071456768, 38760688242913346601269329920, 87159169238118660465556979712,
    2444367727030571407287255040, 38760688242913346601269329920, 2793563116606367322614005760, 2723724038691208139548655616, 2723724038691208139548655616, 2723724038691208139548655616,
    87159169238118660465556979712, 2723724038691208139548655616, 3142758506182163237940756480, 3282436662012481604071456768
  ]
def negativeScales : Array ℕ := #[
    14, 14, 14, 14, 15, 15,
    24, 32, 37, 32, 26, 30,
    15, 35, 20, 15, 36, 14,
    14, 19, 15, 20, 19, 31,
    15, 15, 15, 20, 19, 17,
    20, 23, 19, 19, 23, 17,
    19, 19, 19, 19, 19, 20,
    20, 25, 32, 38, 32, 27,
    19, 18, 16, 19, 22, 19,
    18, 22, 16, 19, 19, 19,
    19, 19, 19, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14938247200400131, 14938247200400131, 14938247200400131, 14938247200400131, 15144698069331655, 15207433824679617,
    24739989609855723, 32058732986931364, 37377555398731508, 32058732986931364, 26739824984415178, 30549691435883801,
    15632739659425936, 35732719365045167, 20261786189207869, 15287604173363601, 36732610325114775, 14326078321178237,
    14326078321178237, 19406825735062607, 15207433824679617, 20261786189207869, 19406825735062607, 31553647109974669,
    15287604173363601, 15207433824679617, 15632739659425936, 20199050433859907, 19836480355810319, 17029125432417594,
    20261786189207869, 23823541299803889, 19992599577423370, 19836480355810319, 23823541299803889, 17029125432417594,
    19992599577423370, 19992599577423370, 19992599577423370, 19992599577423370, 19992599577423370, 20199050433859907,
    20261786189207869, 25591666862722697, 32910410245231846, 38229232651774404, 32910410245231846, 27591502237282789,
    19344089979714636, 18981519917909408, 16174164978272323, 19406825735062607, 22968580858840259, 19137639102247209,
    18981519917909408, 22968580858840259, 16174164978272323, 19137639102247209, 19137639102247209, 19137639102247209,
    19137639102247209, 19137639102247209, 19344089979714636, 19406825735062607
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
noncomputable def negativeCeiling : ℝ := 419409951 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 516890663219449159256899584, coefficient := (-516890663219449159256899584) }, { argument := 82520143503213812445911973888, coefficient := (-82520143503213812445911973888) }, { argument := 823426938297281487437832388608, coefficient := (-823426938297281487437832388608) }, { argument := 82520143503213812445911973888, coefficient := (-82520143503213812445911973888) }, { argument := 516831684366959491392995328, coefficient := (-516831684366959491392995328) }, { argument := 7248250791625366806466658304, coefficient := (-7248250791625366806466658304) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 263317720393902770373739413504, coefficient := (-263317720393902770373739413504) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 263297819403065852938835460096, coefficient := (-263297819403065852938835460096) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 7268151782462284241370611712, coefficient := (-7268151782462284241370611712) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 932779702591419747164749824, coefficient := (-932779702591419747164749824) }, { argument := 148915661264420328206990573568, coefficient := (-148915661264420328206990573568) }, { argument := 1485954359915783833652180287488, coefficient := (-1485954359915783833652180287488) }, { argument := 148915661264420328206990573568, coefficient := (-148915661264420328206990573568) }, { argument := 932673269489800461479313408, coefficient := (-932673269489800461479313408) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 2793563116606367322614005760, coefficient := (-2793563116606367322614005760) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
