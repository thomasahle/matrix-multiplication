import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6

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
def constantNumerator : ℤ := (-48793063240412304211007219171328)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    70418511835, 785397012701, 196355858321, 70413151137, 40115921943, 1372810231783,
    3691836167895, 171929367407, 21218095767, 40115921943, 1502402303463, 1502244045945,
    40114766217, 978983141645, 10918867992187, 2729808825127, 978908615319, 1502402303463,
    53425256861039, 18003632855103, 13378867237595, 791048742063, 1372810231783, 53425256861039,
    53417312477961, 1372741029793, 70418511835, 978983141645, 282049765255, 282049765255,
    3145778535953, 786471089813, 282028293861, 1502244045945, 53417312477961, 144007252154349,
    6688440547443, 790969563801, 3691836167895, 18003632855103, 144007252154349, 922911208401,
    785397012701, 10918867992187, 3145778535953, 40114766217, 1372741029793, 922911208401,
    343841445217, 21217537569, 171929367407, 13378867237595, 6688440547443, 343841445217,
    196355858321, 2729808825127, 786471089813, 21218095767, 791048742063, 790969563801,
    21217537569, 70413151137, 978908615319, 282028293861
  ]
def negativeCoefficients : Array ℕ := #[
    158568391830045431252910080, 7074227387476248628289339392, 7074465362931756050811977728, 158556320611287808371326976, 11291628194632418992324608, 386411728019270190285979648,
    4156637997511210477006356480, 387150517494105150047911936, 11944726023721587314786304, 11291628194632418992324608, 422888653377283853257801728, 422844107846090517035089920,
    11291302886683485092708352, 551118513989302438057738240, 24587104910460504514941157376, 24587932015269297356206505984, 551076559397552076544278528, 422888653377283853257801728,
    15037872930721767199902531584, 162162308435114179609730482176, 15063265376468044793281249280, 445320852498353300655046656, 386411728019270190285979648, 15037872930721767199902531584,
    15035636785679906620273852416, 386392249390746609236574208, 158568391830045431252910080, 551118513989302438057738240, 158779902212794233714114560, 158779902212794233714114560,
    7083663521154017626993721344, 7083901814038989385284714496, 158767814892542043076165632, 422844107846090517035089920, 15035636785679906620273852416, 162137751785243803430500171776,
    15061029178577005536413220864, 445276279099448420217126912, 4156637997511210477006356480, 162162308435114179609730482176, 162137751785243803430500171776, 4156422574250797777494736896,
    7074227387476248628289339392, 24587104910460504514941157376, 7083663521154017626993721344, 11291302886683485092708352, 386392249390746609236574208, 4156422574250797777494736896,
    387131051138453503536529408, 11944411786183487445270528, 387150517494105150047911936, 15063265376468044793281249280, 15061029178577005536413220864, 387131051138453503536529408,
    7074465362931756050811977728, 24587932015269297356206505984, 7083901814038989385284714496, 11944726023721587314786304, 445320852498353300655046656, 445276279099448420217126912,
    11944411786183487445270528, 158556320611287808371326976, 551076559397552076544278528, 158767814892542043076165632
  ]
def negativeScales : Array ℕ := #[
    36, 39, 37, 36, 35, 40,
    41, 37, 34, 35, 40, 40,
    35, 39, 43, 41, 39, 40,
    45, 44, 43, 39, 40, 45,
    45, 40, 36, 39, 38, 38,
    41, 39, 38, 40, 45, 47,
    42, 39, 41, 44, 47, 39,
    39, 43, 41, 35, 40, 39,
    38, 34, 37, 43, 42, 38,
    37, 41, 39, 34, 39, 39,
    34, 36, 39, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36035235687705576, 39514631154409421, 37514679685537435, 36035125856546008, 35223455902489627, 40320269349284622,
    41747475670986267, 37323025037638978, 34304576135249862, 35223455902489627, 40450408318675045, 40450256342495447,
    35223414338339869, 39832493061439660, 43311888526907698, 41311937058035711, 39832383230277446, 40450408318675045,
    45602587172716180, 44033353283047276, 43605021204537588, 39524975635761910, 40320269349284622, 45602587172716180,
    45602372626732056, 40320196622638276, 36035235687705576, 39832493061439660, 38037158779974855, 38037158779974855,
    41516554246678728, 39516602777806742, 38037048948815287, 40450256342495447, 45602372626732056, 47033134795532765,
    42604807015182318, 39524831225187636, 41747475670986267, 44033353283047276, 47033134795532765, 39747400899470211,
    39514631154409421, 43311888526907698, 41516554246678728, 35223414338339869, 40320196622638276, 39747400899470211,
    38322952495515010, 34304538180850544, 37323025037638978, 43605021204537588, 42604807015182318, 38322952495515010,
    37514679685537435, 41311937058035711, 39516602777806742, 34304576135249862, 39524975635761910, 39524831225187636,
    34304538180850544, 36035125856546008, 39832383230277446, 38037048948815287
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
noncomputable def negativeCeiling : ℝ := 254867799 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158568391830045431252910080, coefficient := (-158568391830045431252910080) }, { argument := 7074227387476248628289339392, coefficient := (-7074227387476248628289339392) }, { argument := 7074465362931756050811977728, coefficient := (-7074465362931756050811977728) }, { argument := 158556320611287808371326976, coefficient := (-158556320611287808371326976) }, { argument := 11291628194632418992324608, coefficient := (-11291628194632418992324608) }, { argument := 386411728019270190285979648, coefficient := (-386411728019270190285979648) }, { argument := 4156637997511210477006356480, coefficient := (-4156637997511210477006356480) }, { argument := 387150517494105150047911936, coefficient := (-387150517494105150047911936) }, { argument := 11944726023721587314786304, coefficient := (-11944726023721587314786304) }, { argument := 11291628194632418992324608, coefficient := (-11291628194632418992324608) }, { argument := 422888653377283853257801728, coefficient := (-422888653377283853257801728) }, { argument := 422844107846090517035089920, coefficient := (-422844107846090517035089920) }, { argument := 11291302886683485092708352, coefficient := (-11291302886683485092708352) }, { argument := 551118513989302438057738240, coefficient := (-551118513989302438057738240) }, { argument := 24587104910460504514941157376, coefficient := (-24587104910460504514941157376) }, { argument := 24587932015269297356206505984, coefficient := (-24587932015269297356206505984) }, { argument := 551076559397552076544278528, coefficient := (-551076559397552076544278528) }, { argument := 422888653377283853257801728, coefficient := (-422888653377283853257801728) }, { argument := 15037872930721767199902531584, coefficient := (-15037872930721767199902531584) }, { argument := 162162308435114179609730482176, coefficient := (-162162308435114179609730482176) }, { argument := 15063265376468044793281249280, coefficient := (-15063265376468044793281249280) }, { argument := 445320852498353300655046656, coefficient := (-445320852498353300655046656) }, { argument := 386411728019270190285979648, coefficient := (-386411728019270190285979648) }, { argument := 15037872930721767199902531584, coefficient := (-15037872930721767199902531584) }, { argument := 15035636785679906620273852416, coefficient := (-15035636785679906620273852416) }, { argument := 386392249390746609236574208, coefficient := (-386392249390746609236574208) }, { argument := 158568391830045431252910080, coefficient := (-158568391830045431252910080) }, { argument := 551118513989302438057738240, coefficient := (-551118513989302438057738240) }, { argument := 158779902212794233714114560, coefficient := (-158779902212794233714114560) }, { argument := 158779902212794233714114560, coefficient := (-158779902212794233714114560) }, { argument := 7083663521154017626993721344, coefficient := (-7083663521154017626993721344) }, { argument := 7083901814038989385284714496, coefficient := (-7083901814038989385284714496) }, { argument := 158767814892542043076165632, coefficient := (-158767814892542043076165632) }, { argument := 422844107846090517035089920, coefficient := (-422844107846090517035089920) }, { argument := 15035636785679906620273852416, coefficient := (-15035636785679906620273852416) }, { argument := 162137751785243803430500171776, coefficient := (-162137751785243803430500171776) }, { argument := 15061029178577005536413220864, coefficient := (-15061029178577005536413220864) }, { argument := 445276279099448420217126912, coefficient := (-445276279099448420217126912) }, { argument := 4156637997511210477006356480, coefficient := (-4156637997511210477006356480) }, { argument := 162162308435114179609730482176, coefficient := (-162162308435114179609730482176) }, { argument := 162137751785243803430500171776, coefficient := (-162137751785243803430500171776) }, { argument := 4156422574250797777494736896, coefficient := (-4156422574250797777494736896) }, { argument := 7074227387476248628289339392, coefficient := (-7074227387476248628289339392) }, { argument := 24587104910460504514941157376, coefficient := (-24587104910460504514941157376) }, { argument := 7083663521154017626993721344, coefficient := (-7083663521154017626993721344) }, { argument := 11291302886683485092708352, coefficient := (-11291302886683485092708352) }, { argument := 386392249390746609236574208, coefficient := (-386392249390746609236574208) }, { argument := 4156422574250797777494736896, coefficient := (-4156422574250797777494736896) }, { argument := 387131051138453503536529408, coefficient := (-387131051138453503536529408) }, { argument := 11944411786183487445270528, coefficient := (-11944411786183487445270528) }, { argument := 387150517494105150047911936, coefficient := (-387150517494105150047911936) }, { argument := 15063265376468044793281249280, coefficient := (-15063265376468044793281249280) }, { argument := 15061029178577005536413220864, coefficient := (-15061029178577005536413220864) }, { argument := 387131051138453503536529408, coefficient := (-387131051138453503536529408) }, { argument := 7074465362931756050811977728, coefficient := (-7074465362931756050811977728) }, { argument := 24587932015269297356206505984, coefficient := (-24587932015269297356206505984) }, { argument := 7083901814038989385284714496, coefficient := (-7083901814038989385284714496) }, { argument := 11944726023721587314786304, coefficient := (-11944726023721587314786304) }, { argument := 445320852498353300655046656, coefficient := (-445320852498353300655046656) }, { argument := 445276279099448420217126912, coefficient := (-445276279099448420217126912) }, { argument := 11944411786183487445270528, coefficient := (-11944411786183487445270528) }, { argument := 158556320611287808371326976, coefficient := (-158556320611287808371326976) }, { argument := 551076559397552076544278528, coefficient := (-551076559397552076544278528) }, { argument := 158767814892542043076165632, coefficient := (-158767814892542043076165632) }] }

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
def constantNumerator : ℤ := 51669721965207537770879380357120
def positiveArguments : Array ℕ := #[
    3, 382907, 5323309, 1533671, 1048931, 40897219,
    40891053, 1048877, 183873, 6531961, 2201049, 1635757,
    96825, 183905, 2051143, 512803, 183891
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 28931634925698675837451108352, 100554463998233312771499360256, 28970226104596686578137432064, 9906873194485879647294717952, 386263312496359257513654222848,
    386205076272892509048878923776, 9906363178905729725611638784, 1736631384609380548755849216, 61692627387623381239397875712, 665226241584239982589463494656, 61797152247355217966557822976,
    1828972538815413591264460800, 1736933616064284206049525760, 77489991638181541540448436224, 77492598384480085584606396416, 1736801389802763855983542272
  ]
def positiveScales : Array ℕ := #[
    1, 18, 22, 20, 20, 25,
    25, 20, 17, 22, 21, 20,
    16, 17, 20, 18, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 792281625142643375935439503360, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 18546634509064548, 22343891881563339, 20548557601333823, 20000488348066925, 25285499407835340,
    25285281878905545, 20000414074794799, 17488350123703314, 22639084746433043, 21069759832350155, 20641527013853694,
    16563091975802948, 17488601178640939, 20967996644475525, 18968045175602842, 17488491347481371
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2321928094887363, 2321928094887363, 0
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
noncomputable def positiveFloor : ℝ := 134569837 / 250000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 28931634925698675837451108352, coefficient := 28931634925698675837451108352 }, { argument := 100554463998233312771499360256, coefficient := 100554463998233312771499360256 }, { argument := 28970226104596686578137432064, coefficient := 28970226104596686578137432064 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 9906873194485879647294717952, coefficient := 9906873194485879647294717952 }, { argument := 386263312496359257513654222848, coefficient := 386263312496359257513654222848 }, { argument := 386205076272892509048878923776, coefficient := 386205076272892509048878923776 }, { argument := 9906363178905729725611638784, coefficient := 9906363178905729725611638784 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1736631384609380548755849216, coefficient := 1736631384609380548755849216 }, { argument := 61692627387623381239397875712, coefficient := 61692627387623381239397875712 }, { argument := 665226241584239982589463494656, coefficient := 665226241584239982589463494656 }, { argument := 61797152247355217966557822976, coefficient := 61797152247355217966557822976 }, { argument := 1828972538815413591264460800, coefficient := 1828972538815413591264460800 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1736933616064284206049525760, coefficient := 1736933616064284206049525760 }, { argument := 77489991638181541540448436224, coefficient := 77489991638181541540448436224 }, { argument := 77492598384480085584606396416, coefficient := 77492598384480085584606396416 }, { argument := 1736801389802763855983542272, coefficient := 1736801389802763855983542272 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6
