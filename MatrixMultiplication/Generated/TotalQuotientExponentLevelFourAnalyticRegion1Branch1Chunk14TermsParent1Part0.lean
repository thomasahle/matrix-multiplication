import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 14, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14

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
def constantNumerator : ℤ := (-46106383300051299354690759688192)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92753, 1196467, 1196035, 1195027, 1196035, 10537,
    42025, 20869, 42025, 15141453, 16791609, 535518939,
    7087803, 693129, 7087803, 14153247, 474771, 16791609,
    693129, 10841025, 20513097, 20512905, 20512457, 20512905,
    110253, 439725, 218361, 439725, 799333497, 7938641511,
    18535637583, 3350931237, 327693591, 3350931237, 6691291713, 400050891,
    7938641511, 327693591, 4883, 19475, 9671, 19475,
    252705753, 11421840303, 31756815, 6990879, 2412923013, 22589575,
    58257325, 48745925, 1363696975, 9650504279, 48745925, 43990225,
    22589575, 22589575, 43990225, 1363696975, 43990225, 6990807,
    58257325, 2968095, 41026179, 41025795
  ]
def negativeCoefficients : Array ℕ := #[
    14016437068339462480190242816, 1412538914664898949973803008, 1412028899084749028290723840, 1410838862731065877696872448, 1412028899084749028290723840, 199038302519989806466859008,
    198457451442596840105574400, 197102132262013251929243648, 198457451442596840105574400, 34913813549387713930592256, 309750513808797970301190144, 1234822601794684609445756928,
    261493775971741562145079296, 12785973273066227802046464, 261493775971741562145079296, 261081325220997490280497152, 35031916522476630121119744, 309750513808797970301190144,
    12785973273066227802046464, 51195293099951895502808678400, 48435180866326935312065888256, 48434727519144579826125373440, 48433669709052417025597505536, 48434727519144579826125373440,
    2082620287343307974982500352, 2076542601679854741592473600, 2062361335131797197015744512, 2076542601679854741592473600, 1843137556087785206939910144, 36610522061585972553993682944,
    42740270342079160894950998016, 30906885468768983487659114496, 1511219951942962915011723264, 30906885468768983487659114496, 30858136438061145974271639552, 1844909100684118949797822464,
    36610522061585972553993682944, 1511219951942962915011723264, 184474524286819820627820544, 183936174507772681073459200, 182680025023329355446616064, 183936174507772681073459200,
    582699793943132468051705856, 26336970615027769920460947456, 585809838901140594402263040, 257917911526541112983420928, 22255286645187572686078869504, 104176027189716861111500800,
    134332245586740163012198400, 1798407206222480549714329600, 3144471136489611570918195200, 22252547827118989909172420608, 1798407206222480549714329600, 101434552789987470029619200,
    104176027189716861111500800, 104176027189716861111500800, 101434552789987470029619200, 3144471136489611570918195200, 101434552789987470029619200, 257915255195394498807988224,
    134332245586740163012198400, 14016432345972979610545029120, 48435163157452624550896336896, 48434709810270269064955822080
  ]
def negativeScales : Array ℕ := #[
    16, 20, 20, 20, 20, 13,
    15, 14, 15, 23, 24, 28,
    22, 19, 22, 23, 18, 24,
    19, 23, 24, 24, 24, 24,
    16, 18, 17, 18, 29, 32,
    34, 31, 28, 31, 32, 28,
    32, 28, 12, 14, 13, 14,
    27, 33, 24, 22, 31, 24,
    25, 25, 30, 33, 25, 25,
    24, 24, 25, 30, 25, 22,
    25, 21, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16501106324519055, 20190349175483579, 20189828177578928, 20188611783618950, 20189828177578928, 13363176553811964,
    15358960199010894, 14349073850693780, 15358960199010894, 23852000321487339, 24001237142556879, 28996362379230506,
    22756907075443343, 19402764355429489, 22756907075443343, 23754629734719690, 18856872291268380, 24001237142556879,
    19402764355429489, 23369997831651248, 24290041985831383, 24290028482324614, 24289996973650621, 24290028482324614,
    16750458386920568, 18746242032099458, 17736355683741649, 18746242032099458, 29574222307417462, 32886245006696804,
    34109582690252000, 31641914935933328, 28287772216163475, 31641914935933328, 32639637595221273, 28575608297909707,
    32886245006696804, 28287772216163475, 12253552062637464, 14249335707836394, 13239449359519281, 14249335707836394,
    27912883273077072, 33411076067360029, 24920562897395069, 22737042434137255, 31168134739479843, 24429153792350249,
    25795936123616380, 25538778283525669, 30344875954922468, 33167957185154980, 25538778283525669, 25390679644535597,
    24429153792350249, 24429153792350249, 25390679644535597, 30344875954922468, 25390679644535597, 22737027575551054,
    25795936123616380, 21501105838451461, 25290041458353022, 25290027954841316
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
noncomputable def negativeCeiling : ℝ := 91103 / 400000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14016437068339462480190242816, coefficient := (-14016437068339462480190242816) }, { argument := 1412538914664898949973803008, coefficient := (-1412538914664898949973803008) }, { argument := 1412028899084749028290723840, coefficient := (-1412028899084749028290723840) }, { argument := 1410838862731065877696872448, coefficient := (-1410838862731065877696872448) }, { argument := 1412028899084749028290723840, coefficient := (-1412028899084749028290723840) }, { argument := 199038302519989806466859008, coefficient := (-199038302519989806466859008) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 197102132262013251929243648, coefficient := (-197102132262013251929243648) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 34913813549387713930592256, coefficient := (-34913813549387713930592256) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 1234822601794684609445756928, coefficient := (-1234822601794684609445756928) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 261493775971741562145079296, coefficient := (-261493775971741562145079296) }, { argument := 261081325220997490280497152, coefficient := (-261081325220997490280497152) }, { argument := 35031916522476630121119744, coefficient := (-35031916522476630121119744) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 51195293099951895502808678400, coefficient := (-51195293099951895502808678400) }, { argument := 48435180866326935312065888256, coefficient := (-48435180866326935312065888256) }, { argument := 48434727519144579826125373440, coefficient := (-48434727519144579826125373440) }, { argument := 48433669709052417025597505536, coefficient := (-48433669709052417025597505536) }, { argument := 48434727519144579826125373440, coefficient := (-48434727519144579826125373440) }, { argument := 2082620287343307974982500352, coefficient := (-2082620287343307974982500352) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 2062361335131797197015744512, coefficient := (-2062361335131797197015744512) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 1843137556087785206939910144, coefficient := (-1843137556087785206939910144) }, { argument := 36610522061585972553993682944, coefficient := (-36610522061585972553993682944) }, { argument := 42740270342079160894950998016, coefficient := (-42740270342079160894950998016) }, { argument := 30906885468768983487659114496, coefficient := (-30906885468768983487659114496) }, { argument := 1511219951942962915011723264, coefficient := (-1511219951942962915011723264) }, { argument := 30906885468768983487659114496, coefficient := (-30906885468768983487659114496) }, { argument := 30858136438061145974271639552, coefficient := (-30858136438061145974271639552) }, { argument := 1844909100684118949797822464, coefficient := (-1844909100684118949797822464) }, { argument := 36610522061585972553993682944, coefficient := (-36610522061585972553993682944) }, { argument := 1511219951942962915011723264, coefficient := (-1511219951942962915011723264) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 26336970615027769920460947456, coefficient := (-26336970615027769920460947456) }, { argument := 585809838901140594402263040, coefficient := (-585809838901140594402263040) }, { argument := 257917911526541112983420928, coefficient := (-257917911526541112983420928) }, { argument := 22255286645187572686078869504, coefficient := (-22255286645187572686078869504) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 134332245586740163012198400, coefficient := (-134332245586740163012198400) }, { argument := 1798407206222480549714329600, coefficient := (-1798407206222480549714329600) }, { argument := 3144471136489611570918195200, coefficient := (-3144471136489611570918195200) }, { argument := 22252547827118989909172420608, coefficient := (-22252547827118989909172420608) }, { argument := 1798407206222480549714329600, coefficient := (-1798407206222480549714329600) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 104176027189716861111500800, coefficient := (-104176027189716861111500800) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 3144471136489611570918195200, coefficient := (-3144471136489611570918195200) }, { argument := 101434552789987470029619200, coefficient := (-101434552789987470029619200) }, { argument := 257915255195394498807988224, coefficient := (-257915255195394498807988224) }, { argument := 134332245586740163012198400, coefficient := (-134332245586740163012198400) }, { argument := 14016432345972979610545029120, coefficient := (-14016432345972979610545029120) }, { argument := 48435163157452624550896336896, coefficient := (-48435163157452624550896336896) }, { argument := 48434709810270269064955822080, coefficient := (-48434709810270269064955822080) }] }

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
def constantNumerator : ℤ := (-251653760189486581837760844267520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    41024899, 41025795, 12458180271, 301344501909, 229183089513, 127198677903,
    12438987429, 127198677903, 253996098147, 12458282709, 301344501909, 12438987429,
    4883, 19475, 9671, 19475, 79970175, 3614506425,
    10049625, 628146903, 3678403491, 3961999225, 10217787475, 8549577275,
    239179637425, 14505088553, 8549577275, 7715472175, 3961999225, 3961999225,
    7715472175, 239179637425, 7715472175, 628146849, 10217787475, 9596421,
    433740771, 1205955, 2710749, 475439907, 118859991, 677673,
    15141453, 799333497, 252705753, 12458180271, 79970175, 9596421,
    252705753, 502212699, 79970175, 7750709361, 495815085, 1598667893,
    252705753, 9596421, 495815085, 9596421, 252705753, 252705753,
    15141453, 9509, 37925, 18833
  ]
def negativeCoefficients : Array ℕ := #[
    48433652000178106264427954176, 48434709810270269064955822080, 14363303942704656607919210496, 347426556545925150853702877184, 264230112391773652373301362688, 293300182223856918297267142656,
    14341176102428335121790664704, 293300182223856918297267142656, 292837563639907617164306153472, 14363422045677745524109737984, 347426556545925150853702877184, 14341176102428335121790664704,
    184474524286819820627820544, 183936174507772681073459200, 182680025023329355446616064, 183936174507772681073459200, 368797337938691435475763200, 16668968743688461974975283200,
    370765720823506705317888000, 23174530320668517138218090496, 33927283899158387992169545728, 18271496430952646594422374400, 23560613818859991661228851200, 315423727860656214893186252800,
    551510694902702253784275353600, 33446457037960625674000531456, 315423727860656214893186252800, 17790667577506524315621785600, 18271496430952646594422374400, 18271496430952646594422374400,
    17790667577506524315621785600, 551510694902702253784275353600, 17790667577506524315621785600, 23174528328420157177586515968, 23560613818859991661228851200, 22127840276321486128545792,
    1000138124621307718498516992, 22245943249410402319073280, 100008986102128186667040768, 17540636573714540730645479424, 17540638676643365133534363648, 100006883173303783778156544,
    34913813549387713930592256, 1843137556087785206939910144, 582699793943132468051705856, 14363303942704656607919210496, 368797337938691435475763200, 22127840276321486128545792,
    582699793943132468051705856, 579011820563745553696948224, 368797337938691435475763200, 8935959498254493481577742336, 571635873804971724987432960, 1843138592564217848495341568,
    582699793943132468051705856, 22127840276321486128545792, 571635873804971724987432960, 22127840276321486128545792, 582699793943132468051705856, 582699793943132468051705856,
    34913813549387713930592256, 179619931542429825348141056, 179095748862831294729420800, 177872655943768056619073536
  ]
def negativeScales : Array ℕ := #[
    25, 25, 33, 38, 37, 36,
    33, 36, 37, 33, 38, 33,
    12, 14, 13, 14, 26, 31,
    23, 29, 31, 31, 33, 32,
    37, 33, 32, 32, 31, 31,
    32, 37, 32, 29, 33, 23,
    28, 20, 21, 28, 26, 19,
    23, 29, 27, 33, 26, 23,
    27, 28, 26, 32, 28, 30,
    27, 23, 28, 23, 27, 27,
    23, 13, 15, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25289996446155803, 25290027954841316, 33536374302490780, 38132622786532506, 37737709641361609, 36888292722692984,
    33534149999405926, 36888292722692984, 37886015381838274, 33536386165072939, 38132622786532506, 33534149999405926,
    12253552062637464, 14249335707836394, 13239449359519281, 14249335707836394, 26252958709182194, 31751151509188247,
    23260638332706879, 29226526756822786, 31776432594746208, 31883581455254742, 33250363782682163, 32993205964421896,
    37799303615219701, 33755840052288746, 32993205964421896, 32845107305773121, 31883581455254742, 31883581455254742,
    32845107305773121, 37799303615219701, 32845107305773121, 29226526632798397, 33250363782682163, 23194065020128625,
    28692257819964341, 20201744643653310, 21370260103296661, 28824687764016880, 26824687936980093, 19370229766853884,
    23852000321487339, 29574222307417462, 27912883273077072, 33536374302490780, 26252958709182194, 23194065020128625,
    27912883273077072, 28903723272967495, 26252958709182194, 32851681210647364, 28885226928024954, 30574223118707419,
    27912883273077072, 23194065020128625, 28885226928024954, 23194065020128625, 27912883273077072, 27912883273077072,
    23852000321487339, 13215077914822828, 15210861560021759, 14200975211704646
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
noncomputable def negativeCeiling : ℝ := 177338723 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48433652000178106264427954176, coefficient := (-48433652000178106264427954176) }, { argument := 48434709810270269064955822080, coefficient := (-48434709810270269064955822080) }, { argument := 14363303942704656607919210496, coefficient := (-14363303942704656607919210496) }, { argument := 347426556545925150853702877184, coefficient := (-347426556545925150853702877184) }, { argument := 264230112391773652373301362688, coefficient := (-264230112391773652373301362688) }, { argument := 293300182223856918297267142656, coefficient := (-293300182223856918297267142656) }, { argument := 14341176102428335121790664704, coefficient := (-14341176102428335121790664704) }, { argument := 293300182223856918297267142656, coefficient := (-293300182223856918297267142656) }, { argument := 292837563639907617164306153472, coefficient := (-292837563639907617164306153472) }, { argument := 14363422045677745524109737984, coefficient := (-14363422045677745524109737984) }, { argument := 347426556545925150853702877184, coefficient := (-347426556545925150853702877184) }, { argument := 14341176102428335121790664704, coefficient := (-14341176102428335121790664704) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 368797337938691435475763200, coefficient := (-368797337938691435475763200) }, { argument := 16668968743688461974975283200, coefficient := (-16668968743688461974975283200) }, { argument := 370765720823506705317888000, coefficient := (-370765720823506705317888000) }, { argument := 23174530320668517138218090496, coefficient := (-23174530320668517138218090496) }, { argument := 33927283899158387992169545728, coefficient := (-33927283899158387992169545728) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 23560613818859991661228851200, coefficient := (-23560613818859991661228851200) }, { argument := 315423727860656214893186252800, coefficient := (-315423727860656214893186252800) }, { argument := 551510694902702253784275353600, coefficient := (-551510694902702253784275353600) }, { argument := 33446457037960625674000531456, coefficient := (-33446457037960625674000531456) }, { argument := 315423727860656214893186252800, coefficient := (-315423727860656214893186252800) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 18271496430952646594422374400, coefficient := (-18271496430952646594422374400) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 551510694902702253784275353600, coefficient := (-551510694902702253784275353600) }, { argument := 17790667577506524315621785600, coefficient := (-17790667577506524315621785600) }, { argument := 23174528328420157177586515968, coefficient := (-23174528328420157177586515968) }, { argument := 23560613818859991661228851200, coefficient := (-23560613818859991661228851200) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 1000138124621307718498516992, coefficient := (-1000138124621307718498516992) }, { argument := 22245943249410402319073280, coefficient := (-22245943249410402319073280) }, { argument := 100008986102128186667040768, coefficient := (-100008986102128186667040768) }, { argument := 17540636573714540730645479424, coefficient := (-17540636573714540730645479424) }, { argument := 17540638676643365133534363648, coefficient := (-17540638676643365133534363648) }, { argument := 100006883173303783778156544, coefficient := (-100006883173303783778156544) }, { argument := 34913813549387713930592256, coefficient := (-34913813549387713930592256) }, { argument := 1843137556087785206939910144, coefficient := (-1843137556087785206939910144) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 14363303942704656607919210496, coefficient := (-14363303942704656607919210496) }, { argument := 368797337938691435475763200, coefficient := (-368797337938691435475763200) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 368797337938691435475763200, coefficient := (-368797337938691435475763200) }, { argument := 8935959498254493481577742336, coefficient := (-8935959498254493481577742336) }, { argument := 571635873804971724987432960, coefficient := (-571635873804971724987432960) }, { argument := 1843138592564217848495341568, coefficient := (-1843138592564217848495341568) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 571635873804971724987432960, coefficient := (-571635873804971724987432960) }, { argument := 22127840276321486128545792, coefficient := (-22127840276321486128545792) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 582699793943132468051705856, coefficient := (-582699793943132468051705856) }, { argument := 34913813549387713930592256, coefficient := (-34913813549387713930592256) }, { argument := 179619931542429825348141056, coefficient := (-179619931542429825348141056) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
