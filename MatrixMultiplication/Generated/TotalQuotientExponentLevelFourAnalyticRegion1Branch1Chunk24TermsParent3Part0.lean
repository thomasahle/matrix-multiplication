import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 24, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24

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
def constantNumerator : ℤ := (-61271951444432446583808074973184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    776517, 41, 12333919, 429, 19, 24667829,
    19, 37, 699, 37, 429, 699,
    97065, 37, 37, 41, 6116685, 35,
    29, 934456573, 195, 195733859, 781, 781,
    559, 29, 6116685, 6214451, 6116685, 6214451,
    6214451, 726348675, 198862365, 35, 35, 629061,
    29, 29, 6116685, 35, 29, 934456573,
    195, 195733859, 781, 781, 559, 29,
    934456573, 726348675, 934456573, 726348675, 12268383, 195,
    195, 195733859, 198862365, 195733859, 198862365, 24536757,
    6214451, 726348675, 198862365, 781
  ]
def negativeCoefficients : Array ℕ := #[
    3666997854178488292403576832, 793055337667196738607251456, 116490571376058183248928309248, 8298066825834814655183192064, 735026898325694538221355008, 116490528874759837422121385984,
    735026898325694538221355008, 715684085211860471426056192, 27041252733140025379827744768, 715684085211860471426056192, 8298066825834814655183192064, 27041252733140025379827744768,
    3667012021277936901339217920, 715684085211860471426056192, 715684085211860471426056192, 793055337667196738607251456, 3610653528783939479242014720, 5415987671873538702683668480,
    280470790150593968531832832, 17237681250126687000453971968, 7543697114395286050166538240, 3610652403532550982959366144, 7553368520952203083564187648, 7553368520952203083564187648,
    5406316265316621669286019072, 280470790150593968531832832, 3610653528783939479242014720, 3668364388979468695987290112, 3610653528783939479242014720, 3668364388979468695987290112,
    3668364388979468695987290112, 13398768116003035151125708800, 3668363153047615757447331840, 5415987671873538702683668480, 5415987671873538702683668480, 2970656582080461887772819456,
    280470790150593968531832832, 280470790150593968531832832, 3610653528783939479242014720, 5415987671873538702683668480, 280470790150593968531832832, 17237681250126687000453971968,
    7543697114395286050166538240, 3610652403532550982959366144, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 280470790150593968531832832,
    17237681250126687000453971968, 13398768116003035151125708800, 17237681250126687000453971968, 13398768116003035151125708800, 115871601356415493111478747136, 7543697114395286050166538240,
    7543697114395286050166538240, 3610652403532550982959366144, 3668363153047615757447331840, 3610652403532550982959366144, 3668363153047615757447331840, 115871558855117147284671823872,
    3668364388979468695987290112, 13398768116003035151125708800, 3668363153047615757447331840, 7553368520952203083564187648
  ]
def negativeScales : Array ℕ := #[
    19, 5, 23, 8, 4, 24,
    4, 5, 9, 5, 8, 9,
    16, 5, 5, 5, 22, 5,
    4, 29, 7, 27, 9, 9,
    9, 4, 22, 22, 22, 22,
    22, 29, 27, 5, 5, 19,
    4, 4, 22, 5, 4, 29,
    7, 27, 9, 9, 9, 4,
    29, 29, 29, 29, 23, 7,
    7, 27, 27, 27, 27, 24,
    22, 29, 27, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19566657983787216, 5357552004618085, 23556127941125568, 8744833837700333, 4247927513443586, 24556127414761736,
    4247927513443586, 5209453365628950, 9449148645375482, 5209453365628950, 8744833837700333, 9449148645375482,
    16566663557492315, 5209453365628950, 5209453365628950, 5357552004618085, 22544318550707580, 5129283016944967,
    4857980997143165, 29799552378901224, 7607330313756529, 27544318101095111, 9609178738149255, 9609178738149255,
    9126704472843191, 4857980997143165, 22544318550707580, 22567195514978767, 22544318550707580, 22567195514978767,
    22567195514978767, 29436087022109046, 27567195028911172, 5129283016944967, 5129283016944967, 19262840396359288,
    4857980997143165, 4857980997143165, 22544318550707580, 5129283016944967, 4857980997143165, 29799552378901224,
    7607330313756529, 27544318101095111, 9609178738149255, 9609178738149255, 9126704472843191, 4857980997143165,
    29799552378901224, 29436087022109046, 29799552378901224, 29436087022109046, 23548441775348019, 7607330313756529,
    7607330313756529, 27544318101095111, 27567195028911172, 27544318101095111, 27567195028911172, 24548441246172424,
    22567195514978767, 29436087022109046, 27567195028911172, 9609178738149255
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
noncomputable def negativeCeiling : ℝ := 216126073 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3666997854178488292403576832, coefficient := (-3666997854178488292403576832) }, { argument := 793055337667196738607251456, coefficient := (-793055337667196738607251456) }, { argument := 116490571376058183248928309248, coefficient := (-116490571376058183248928309248) }, { argument := 8298066825834814655183192064, coefficient := (-8298066825834814655183192064) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 116490528874759837422121385984, coefficient := (-116490528874759837422121385984) }, { argument := 735026898325694538221355008, coefficient := (-735026898325694538221355008) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 27041252733140025379827744768, coefficient := (-27041252733140025379827744768) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 8298066825834814655183192064, coefficient := (-8298066825834814655183192064) }, { argument := 27041252733140025379827744768, coefficient := (-27041252733140025379827744768) }, { argument := 3667012021277936901339217920, coefficient := (-3667012021277936901339217920) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 793055337667196738607251456, coefficient := (-793055337667196738607251456) }, { argument := 3610653528783939479242014720, coefficient := (-3610653528783939479242014720) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 17237681250126687000453971968, coefficient := (-17237681250126687000453971968) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 3610652403532550982959366144, coefficient := (-3610652403532550982959366144) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 3610653528783939479242014720, coefficient := (-3610653528783939479242014720) }, { argument := 3668364388979468695987290112, coefficient := (-3668364388979468695987290112) }, { argument := 3610653528783939479242014720, coefficient := (-3610653528783939479242014720) }, { argument := 3668364388979468695987290112, coefficient := (-3668364388979468695987290112) }, { argument := 3668364388979468695987290112, coefficient := (-3668364388979468695987290112) }, { argument := 13398768116003035151125708800, coefficient := (-13398768116003035151125708800) }, { argument := 3668363153047615757447331840, coefficient := (-3668363153047615757447331840) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 2970656582080461887772819456, coefficient := (-2970656582080461887772819456) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 3610653528783939479242014720, coefficient := (-3610653528783939479242014720) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 17237681250126687000453971968, coefficient := (-17237681250126687000453971968) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 3610652403532550982959366144, coefficient := (-3610652403532550982959366144) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 17237681250126687000453971968, coefficient := (-17237681250126687000453971968) }, { argument := 13398768116003035151125708800, coefficient := (-13398768116003035151125708800) }, { argument := 17237681250126687000453971968, coefficient := (-17237681250126687000453971968) }, { argument := 13398768116003035151125708800, coefficient := (-13398768116003035151125708800) }, { argument := 115871601356415493111478747136, coefficient := (-115871601356415493111478747136) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 3610652403532550982959366144, coefficient := (-3610652403532550982959366144) }, { argument := 3668363153047615757447331840, coefficient := (-3668363153047615757447331840) }, { argument := 3610652403532550982959366144, coefficient := (-3610652403532550982959366144) }, { argument := 3668363153047615757447331840, coefficient := (-3668363153047615757447331840) }, { argument := 115871558855117147284671823872, coefficient := (-115871558855117147284671823872) }, { argument := 3668364388979468695987290112, coefficient := (-3668364388979468695987290112) }, { argument := 13398768116003035151125708800, coefficient := (-13398768116003035151125708800) }, { argument := 3668363153047615757447331840, coefficient := (-3668363153047615757447331840) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }] }

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
def constantNumerator : ℤ := 61732813309682657059272864563200
def positiveArguments : Array ℕ := #[
    11, 9, 41, 1, 429, 19,
    1, 19, 37, 699, 37, 429,
    699, 9, 37, 37, 41, 7,
    35, 29, 521, 195, 7, 781,
    781, 559, 29, 61, 67, 61,
    67, 3, 1, 1, 1, 92753,
    10841025, 2968095, 629061, 12268383, 24536757, 78633
  ]
def positiveCoefficients : Array ℕ := #[
    871509787656907713528983453696, 696341272098026404630757376, 793055337667196738607251456, 618970019642690137449562112, 8298066825834814655183192064, 735026898325694538221355008,
    618970019642690137449562112, 735026898325694538221355008, 715684085211860471426056192, 27041252733140025379827744768, 715684085211860471426056192, 8298066825834814655183192064,
    27041252733140025379827744768, 696341272098026404630757376, 715684085211860471426056192, 715684085211860471426056192, 793055337667196738607251456, 1083197534374707740536733696,
    21663950687494154810734673920, 1121883160602375874127331328, 20155211264615097600701366272, 30174788457581144200666152960, 1083197534374707740536733696, 30213474083808812334256750592,
    30213474083808812334256750592, 21625265061266486677144076288, 1121883160602375874127331328, 37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832,
    41470991316060239209120661504, 475368975085586025561263702016, 79228162514264337593543950336, 79228162514264337593543950336, 79228162514264337593543950336, 28032874136678924960380485632,
    102390586199903791005617356800, 28032864691945959221090058240, 5941313164160923775545638912, 231743202712830986222957494272, 231743117710234294569343647744, 5941341498359820993416921088
  ]
def positiveScales : Array ℕ := #[
    3, 3, 5, 0, 8, 4,
    0, 4, 5, 9, 5, 8,
    9, 3, 5, 5, 5, 2,
    5, 4, 9, 7, 2, 9,
    9, 9, 4, 5, 6, 5,
    6, 1, 0, 0, 0, 16,
    23, 21, 19, 23, 24, 16
  ]
def negativeArguments : Array ℕ := #[
    781, 781, 781, 559, 559, 78633,
    29, 29, 1, 1, 1, 3,
    1, 1, 1, 3
  ]
def negativeCoefficients : Array ℕ := #[
    7553368520952203083564187648, 7553368520952203083564187648, 7553368520952203083564187648, 5406316265316621669286019072, 5406316265316621669286019072, 2970670749179910496708460544,
    280470790150593968531832832, 280470790150593968531832832, 79228162514264337593543950336, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016,
    79228162514264337593543950336, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    9, 9, 9, 9, 9, 16,
    4, 4, 0, 0, 0, 1,
    0, 0, 0, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 3169925001442312, 5357552004618083, 0, 8744833837487090, 4247927513443585,
    0, 4247927513443585, 5209453365628949, 9449148645375433, 5209453365628949, 8744833837487090,
    9449148645375433, 3169925001442312, 5209453365628949, 5209453365628949, 5357552004618083, 2807354922011143,
    5129283016944966, 4857980995002857, 9025139562278508, 7607330313749179, 2807354922011143, 9609178738141526,
    9609178738141526, 9126704472843189, 4857980995002857, 5930737337099561, 6066089190457772, 5930737337099561,
    6066089190457772, 1584962500720924, 0, 0, 0, 16501106324518755,
    23369997831651245, 21501105838451160, 19262840396359287, 23548441775346671, 24548441246171076, 16262847276574087
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9609178738149255, 9609178738149255, 9609178738149255, 9126704472843191, 9126704472843191, 16262847276574088,
    4857980997143165, 4857980997143165, 0, 0, 0, 1584962500724866,
    0, 0, 0, 1584962500724866
  ]

abbrev PositiveTerm := Fin 42
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 10372357 / 40000000000
noncomputable def negativeCeiling : ℝ := 1128083 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 2970670749179910496708460544, coefficient := (-2970670749179910496708460544) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 871509787656907713528983453696, coefficient := 871509787656907713528983453696 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 793055337667196738607251456, coefficient := 793055337667196738607251456 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 8298066825834814655183192064, coefficient := 8298066825834814655183192064 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 27041252733140025379827744768, coefficient := 27041252733140025379827744768 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 8298066825834814655183192064, coefficient := 8298066825834814655183192064 }, { argument := 27041252733140025379827744768, coefficient := 27041252733140025379827744768 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 793055337667196738607251456, coefficient := 793055337667196738607251456 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1083197534374707740536733696, coefficient := 1083197534374707740536733696 }, { argument := 21663950687494154810734673920, coefficient := 21663950687494154810734673920 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 20155211264615097600701366272, coefficient := 20155211264615097600701366272 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 1083197534374707740536733696, coefficient := 1083197534374707740536733696 }, { argument := 30213474083808812334256750592, coefficient := 30213474083808812334256750592 }, { argument := 30213474083808812334256750592, coefficient := 30213474083808812334256750592 }, { argument := 21625265061266486677144076288, coefficient := 21625265061266486677144076288 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28032874136678924960380485632, coefficient := 28032874136678924960380485632 }, { argument := 102390586199903791005617356800, coefficient := 102390586199903791005617356800 }, { argument := 28032864691945959221090058240, coefficient := 28032864691945959221090058240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5941313164160923775545638912, coefficient := 5941313164160923775545638912 }, { argument := 231743202712830986222957494272, coefficient := 231743202712830986222957494272 }, { argument := 231743117710234294569343647744, coefficient := 231743117710234294569343647744 }, { argument := 5941341498359820993416921088, coefficient := 5941341498359820993416921088 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24
