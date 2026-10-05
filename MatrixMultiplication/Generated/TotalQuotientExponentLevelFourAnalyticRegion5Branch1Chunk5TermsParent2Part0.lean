import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2445099369340987371984806477824)
def positiveArguments : Array ℕ := #[
    17, 6118819, 5330201, 6114809, 533473, 36681763,
    18340891, 1066981, 20585, 2597081, 28199681, 2596543,
    78787
  ]
def positiveCoefficients : Array ℕ := #[
    1346878762742493739090247155712, 115581223041383838627288580096, 402738600789732252603002126336, 115505476282998609518060896256, 20154040117727345928688369664, 692898912495071542491524104192,
    692899271394924240584560345088, 20154701249034947679018287104, 1555358624797946347582914560, 49057473070790324244923285504, 532676913528063838437616123904, 49047310538119188768423411712,
    1488244352343402949805867008
  ]
def positiveScales : Array ℕ := #[
    4, 22, 22, 22, 19, 25,
    24, 20, 14, 21, 24, 21,
    16
  ]
def negativeArguments : Array ℕ := #[
    63107244095, 1986755032675, 10783776751265, 3972829109039, 120713346313, 126738301303,
    8696708315585, 135886148583, 253485074833, 63107244095, 109589393935, 63072959395,
    109589393935, 13841437743619, 150314238165739, 13838278369805, 419555145929, 8696708315585,
    9344125080657, 149506078385525, 8696993444149, 1986755032675, 13841437743619, 3970946644279,
    63072959395, 3970946644279, 43106724463249, 992568475825, 60322383127, 135886148583,
    149506078385525, 18688269434999, 4348499319283, 10783776751265, 150314238165739, 43106724463249,
    253485074833, 8696993444149, 4348499319283, 63373386837, 3972829109039, 13838278369805,
    992568475825, 120713346313, 419555145929, 60322383127, 1, 9,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    142104880495310467036610560, 4473774612415793802405478400, 48565812958643671929391677440, 4473007923768675005508878336, 135911145368468109301645312, 142694641630440111915139072,
    4895811541177312491360747520, 4895814464985685224371257344, 142699411070235136697040896, 142104880495310467036610560, 493546753689424494340341760, 142027678214238212414504960,
    493546753689424494340341760, 15584073466108611837093216256, 169238786747925537140701659136, 15580516327425748211408568320, 472377099716804617957277696, 4895811541177312491360747520,
    168328792925400684323288383488, 168328879726668639054174617600, 4895972054289135376938303488, 4473774612415793802405478400, 15584073466108611837093216256, 4470888456870756482962948096,
    142027678214238212414504960, 4470888456870756482962948096, 48533857057462710148714725376, 4470131017865171167294259200, 135833931086428747644010496, 4895814464985685224371257344,
    168328879726668639054174617600, 168328966527321852435924779008, 4895974978485943577809518592, 48565812958643671929391677440, 169238786747925537140701659136, 48533857057462710148714725376,
    142699411070235136697040896, 4895972054289135376938303488, 4895974978485943577809518592, 142704180672159748064280576, 4473007923768675005508878336, 15580516327425748211408568320,
    4470131017865171167294259200, 135911145368468109301645312, 472377099716804617957277696, 135833931086428747644010496, 633825300114114700748351602688, 1426106925256758076683791106048,
    633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    35, 40, 43, 41, 36, 36,
    42, 36, 37, 35, 36, 35,
    36, 43, 47, 43, 38, 42,
    43, 47, 42, 40, 43, 41,
    35, 41, 45, 39, 35, 36,
    47, 44, 41, 43, 47, 45,
    37, 42, 41, 35, 41, 43,
    39, 36, 38, 35, 0, 3,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 22544821792951004, 22345758506855641, 22543876005271152, 19025055730019180, 25128559643663421,
    24128560390933902, 20025103055280481, 14329305828208631, 21308459580058227, 24749175506881441, 21308160686670961,
    16265669981531174
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35877086573760665, 40853551139444550, 43293927768404699, 41853303877829281, 36812794236805968, 36883061631038776,
    42983606604302676, 36983607465888910, 37883109851017298, 35877086573760665, 36673317224782002, 35876302578028741,
    36673317224782002, 43654059040541050, 47094975000073941, 43653729700967074, 38610069493359643, 42983606604302676,
    43087196724942026, 47087197468889181, 42983653903456424, 40853551139444550, 43654059040541050, 41852620116654817,
    35876302578028741, 41852620116654817, 45292978174614777, 39852375680650488, 35811974375279211, 36983607465888910,
    47087197468889181, 44087198212830683, 41983654765128871, 43293927768404699, 47094975000073941, 45292978174614777,
    37883109851017298, 42983653903456424, 41983654765128871, 35883158071023273, 41853303877829281, 43653729700967074,
    39852375680650488, 36812794236805968, 38610069493359643, 35811974375279211, 0, 3169925001442313,
    0
  ]

abbrev PositiveTerm := Fin 13
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
noncomputable def positiveFloor : ℝ := 33680671 / 40000000000
noncomputable def negativeCeiling : ℝ := 157756719 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 142104880495310467036610560, coefficient := (-142104880495310467036610560) }, { argument := 4473774612415793802405478400, coefficient := (-4473774612415793802405478400) }, { argument := 48565812958643671929391677440, coefficient := (-48565812958643671929391677440) }, { argument := 4473007923768675005508878336, coefficient := (-4473007923768675005508878336) }, { argument := 135911145368468109301645312, coefficient := (-135911145368468109301645312) }, { argument := 142694641630440111915139072, coefficient := (-142694641630440111915139072) }, { argument := 4895811541177312491360747520, coefficient := (-4895811541177312491360747520) }, { argument := 4895814464985685224371257344, coefficient := (-4895814464985685224371257344) }, { argument := 142699411070235136697040896, coefficient := (-142699411070235136697040896) }, { argument := 142104880495310467036610560, coefficient := (-142104880495310467036610560) }, { argument := 493546753689424494340341760, coefficient := (-493546753689424494340341760) }, { argument := 142027678214238212414504960, coefficient := (-142027678214238212414504960) }, { argument := 493546753689424494340341760, coefficient := (-493546753689424494340341760) }, { argument := 15584073466108611837093216256, coefficient := (-15584073466108611837093216256) }, { argument := 169238786747925537140701659136, coefficient := (-169238786747925537140701659136) }, { argument := 15580516327425748211408568320, coefficient := (-15580516327425748211408568320) }, { argument := 472377099716804617957277696, coefficient := (-472377099716804617957277696) }, { argument := 4895811541177312491360747520, coefficient := (-4895811541177312491360747520) }, { argument := 168328792925400684323288383488, coefficient := (-168328792925400684323288383488) }, { argument := 168328879726668639054174617600, coefficient := (-168328879726668639054174617600) }, { argument := 4895972054289135376938303488, coefficient := (-4895972054289135376938303488) }, { argument := 4473774612415793802405478400, coefficient := (-4473774612415793802405478400) }, { argument := 15584073466108611837093216256, coefficient := (-15584073466108611837093216256) }, { argument := 4470888456870756482962948096, coefficient := (-4470888456870756482962948096) }, { argument := 142027678214238212414504960, coefficient := (-142027678214238212414504960) }, { argument := 4470888456870756482962948096, coefficient := (-4470888456870756482962948096) }, { argument := 48533857057462710148714725376, coefficient := (-48533857057462710148714725376) }, { argument := 4470131017865171167294259200, coefficient := (-4470131017865171167294259200) }, { argument := 135833931086428747644010496, coefficient := (-135833931086428747644010496) }, { argument := 4895814464985685224371257344, coefficient := (-4895814464985685224371257344) }, { argument := 168328879726668639054174617600, coefficient := (-168328879726668639054174617600) }, { argument := 168328966527321852435924779008, coefficient := (-168328966527321852435924779008) }, { argument := 4895974978485943577809518592, coefficient := (-4895974978485943577809518592) }, { argument := 48565812958643671929391677440, coefficient := (-48565812958643671929391677440) }, { argument := 169238786747925537140701659136, coefficient := (-169238786747925537140701659136) }, { argument := 48533857057462710148714725376, coefficient := (-48533857057462710148714725376) }, { argument := 142699411070235136697040896, coefficient := (-142699411070235136697040896) }, { argument := 4895972054289135376938303488, coefficient := (-4895972054289135376938303488) }, { argument := 4895974978485943577809518592, coefficient := (-4895974978485943577809518592) }, { argument := 142704180672159748064280576, coefficient := (-142704180672159748064280576) }, { argument := 4473007923768675005508878336, coefficient := (-4473007923768675005508878336) }, { argument := 15580516327425748211408568320, coefficient := (-15580516327425748211408568320) }, { argument := 4470131017865171167294259200, coefficient := (-4470131017865171167294259200) }, { argument := 135911145368468109301645312, coefficient := (-135911145368468109301645312) }, { argument := 472377099716804617957277696, coefficient := (-472377099716804617957277696) }, { argument := 135833931086428747644010496, coefficient := (-135833931086428747644010496) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 115581223041383838627288580096, coefficient := 115581223041383838627288580096 }, { argument := 402738600789732252603002126336, coefficient := 402738600789732252603002126336 }, { argument := 115505476282998609518060896256, coefficient := 115505476282998609518060896256 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 20154040117727345928688369664, coefficient := 20154040117727345928688369664 }, { argument := 692898912495071542491524104192, coefficient := 692898912495071542491524104192 }, { argument := 692899271394924240584560345088, coefficient := 692899271394924240584560345088 }, { argument := 20154701249034947679018287104, coefficient := 20154701249034947679018287104 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1555358624797946347582914560, coefficient := 1555358624797946347582914560 }, { argument := 49057473070790324244923285504, coefficient := 49057473070790324244923285504 }, { argument := 532676913528063838437616123904, coefficient := 532676913528063838437616123904 }, { argument := 49047310538119188768423411712, coefficient := 49047310538119188768423411712 }, { argument := 1488244352343402949805867008, coefficient := 1488244352343402949805867008 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk5
