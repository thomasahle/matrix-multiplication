import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1600248857868154209886280330772480
def positiveArguments : Array ℕ := #[
    47, 257, 1025, 509, 1025, 1,
    5, 5, 5, 5, 899, 21779,
    16501, 9193, 899
  ]
def positiveCoefficients : Array ℕ := #[
    14894894552681695467586262663168, 39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 158456325028528675187087900672,
    198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 198070406285660843983859875840, 34778377978673652097947271168, 842534253612384281469625827328,
    638351518382751872378451525632, 711273923821906304196728061952, 34778377978673652097947271168
  ]
def positiveScales : Array ℕ := #[
    5, 8, 10, 8, 10, 0,
    2, 2, 2, 2, 9, 14,
    14, 13, 9
  ]
def negativeArguments : Array ℕ := #[
    1747683, 16791609, 7938641511, 301344501909, 31754587823, 16791609,
    1195027, 20869, 20512457, 218361, 9671, 41024899,
    9671, 18833, 355791, 18833, 218361, 355791,
    149379, 18833, 18833, 20869, 693129, 327693591,
    12438987429, 1310775263, 693129, 1196035, 42025, 20512905,
    439725, 19475, 41025795, 19475, 37925, 716475,
    37925, 439725, 716475, 149505, 37925, 37925,
    42025, 92753, 10841025, 2968095, 1, 1,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    128956244091891721187622912, 309750513808797970301190144, 36610522061585972553993682944, 347426556545925150853702877184, 36610547171063421386513973248, 309750513808797970301190144,
    1410838862731065877696872448, 197102132262013251929243648, 48433669709052417025597505536, 2062361335131797197015744512, 182680025023329355446616064, 48433652000178106264427954176,
    182680025023329355446616064, 177872655943768056619073536, 6720701973226695760904454144, 177872655943768056619073536, 2062361335131797197015744512, 6720701973226695760904454144,
    1410844765689169464753389568, 177872655943768056619073536, 177872655943768056619073536, 197102132262013251929243648, 12785973273066227802046464, 1511219951942962915011723264,
    14341176102428335121790664704, 1511220988419395556567154688, 12785973273066227802046464, 1412028899084749028290723840, 198457451442596840105574400, 48434727519144579826125373440,
    2076542601679854741592473600, 183936174507772681073459200, 48434709810270269064955822080, 183936174507772681073459200, 179095748862831294729420800, 6766915051628058108965683200,
    179095748862831294729420800, 2076542601679854741592473600, 6766915051628058108965683200, 1412034802042852615347240960, 179095748862831294729420800, 179095748862831294729420800,
    198457451442596840105574400, 14016437068339462480190242816, 51195293099951895502808678400, 14016432345972979610545029120, 158456325028528675187087900672, 158456325028528675187087900672,
    792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    20, 24, 32, 38, 34, 24,
    20, 14, 24, 17, 13, 25,
    13, 14, 18, 14, 17, 18,
    17, 14, 14, 14, 19, 28,
    33, 30, 19, 20, 15, 24,
    18, 14, 25, 14, 15, 19,
    15, 18, 19, 17, 15, 15,
    15, 16, 23, 21, 0, 0,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5554588851677541, 8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 0,
    2321928094887362, 2321928094887362, 2321928094887362, 2321928094887362, 9812177305463258, 14410650092641842,
    14010265837434154, 13166320025266979, 9812177305463258
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    20737012097694363, 24001237142556879, 32886245006696804, 38132622786532506, 34886245996174866, 24001237142556879,
    20188611783618950, 14349073850693780, 24289996973650621, 17736355683741649, 13239449359519281, 25289996446155803,
    13239449359519281, 14200975211704646, 18440670491451165, 14200975211704646, 17736355683741649, 18440670491451165,
    17188617819850863, 14200975211704646, 14200975211704646, 14349073850693780, 19402764355429489, 28287772216163475,
    33534149999405926, 30287773205641476, 19402764355429489, 20189828177578928, 15358960199010894, 24290028482324614,
    18746242032099458, 14249335707836394, 25290027954841316, 14249335707836394, 15210861560021759, 19450556839768293,
    15210861560021759, 18746242032099458, 19450556839768293, 17189834208723607, 15210861560021759, 15210861560021759,
    15358960199010894, 16501106324519055, 23369997831651248, 21501105838451461, 0, 0,
    2321928094887363
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
noncomputable def positiveFloor : ℝ := 1410413693 / 1000000000000
noncomputable def negativeCeiling : ℝ := 6138629 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 128956244091891721187622912, coefficient := (-128956244091891721187622912) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 36610522061585972553993682944, coefficient := (-36610522061585972553993682944) }, { argument := 347426556545925150853702877184, coefficient := (-347426556545925150853702877184) }, { argument := 36610547171063421386513973248, coefficient := (-36610547171063421386513973248) }, { argument := 309750513808797970301190144, coefficient := (-309750513808797970301190144) }, { argument := 1410838862731065877696872448, coefficient := (-1410838862731065877696872448) }, { argument := 197102132262013251929243648, coefficient := (-197102132262013251929243648) }, { argument := 48433669709052417025597505536, coefficient := (-48433669709052417025597505536) }, { argument := 2062361335131797197015744512, coefficient := (-2062361335131797197015744512) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 48433652000178106264427954176, coefficient := (-48433652000178106264427954176) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 6720701973226695760904454144, coefficient := (-6720701973226695760904454144) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 2062361335131797197015744512, coefficient := (-2062361335131797197015744512) }, { argument := 6720701973226695760904454144, coefficient := (-6720701973226695760904454144) }, { argument := 1410844765689169464753389568, coefficient := (-1410844765689169464753389568) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 177872655943768056619073536, coefficient := (-177872655943768056619073536) }, { argument := 197102132262013251929243648, coefficient := (-197102132262013251929243648) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 1511219951942962915011723264, coefficient := (-1511219951942962915011723264) }, { argument := 14341176102428335121790664704, coefficient := (-14341176102428335121790664704) }, { argument := 1511220988419395556567154688, coefficient := (-1511220988419395556567154688) }, { argument := 12785973273066227802046464, coefficient := (-12785973273066227802046464) }, { argument := 1412028899084749028290723840, coefficient := (-1412028899084749028290723840) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 48434727519144579826125373440, coefficient := (-48434727519144579826125373440) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 48434709810270269064955822080, coefficient := (-48434709810270269064955822080) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 2076542601679854741592473600, coefficient := (-2076542601679854741592473600) }, { argument := 6766915051628058108965683200, coefficient := (-6766915051628058108965683200) }, { argument := 1412034802042852615347240960, coefficient := (-1412034802042852615347240960) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 198457451442596840105574400, coefficient := (-198457451442596840105574400) }, { argument := 14016437068339462480190242816, coefficient := (-14016437068339462480190242816) }, { argument := 51195293099951895502808678400, coefficient := (-51195293099951895502808678400) }, { argument := 14016432345972979610545029120, coefficient := (-14016432345972979610545029120) }, { argument := 14894894552681695467586262663168, coefficient := 14894894552681695467586262663168 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 34778377978673652097947271168, coefficient := 34778377978673652097947271168 }, { argument := 842534253612384281469625827328, coefficient := 842534253612384281469625827328 }, { argument := 638351518382751872378451525632, coefficient := 638351518382751872378451525632 }, { argument := 711273923821906304196728061952, coefficient := 711273923821906304196728061952 }, { argument := 34778377978673652097947271168, coefficient := 34778377978673652097947271168 }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-350880132277512297747127388340224)
def positiveArguments : Array ℕ := #[
    9193, 18357, 899, 21779, 899, 147,
    441, 931, 2401, 2009, 56203, 1715,
    2009, 1813, 931, 931, 1813, 56203,
    1813, 147, 2401, 27, 405, 711,
    27, 225, 27, 711, 1413, 225,
    21807, 1395, 405, 711, 27, 1395,
    27, 711, 711, 27, 9, 41,
    1, 429, 19, 1, 19, 37,
    699, 37, 429, 699, 9, 37,
    37, 41, 92753, 10841025, 2968095
  ]
def positiveCoefficients : Array ℕ := #[
    711273923821906304196728061952, 710152040661303928322600730624, 34778377978673652097947271168, 842534253612384281469625827328, 34778377978673652097947271168, 90988592887475450205085630464,
    68241444665606587653814222848, 72032636035918064745692790784, 92884188572631188751024914432, 1243510769462164486136170283008, 2174248250873632112192358711296, 66345848980450849107874938880,
    1243510769462164486136170283008, 70137040350762326199753506816, 72032636035918064745692790784, 72032636035918064745692790784, 70137040350762326199753506816, 2174248250873632112192358711296,
    70137040350762326199753506816, 90988592887475450205085630464, 92884188572631188751024914432, 2089023816294079213892272128, 31335357244411188208384081920, 55010960495744085965829832704,
    2089023816294079213892272128, 34817063604901320231537868800, 2089023816294079213892272128, 55010960495744085965829832704, 54662789859695072763514454016, 34817063604901320231537868800,
    843617451146758989210162561024, 53966448587597046358883696640, 31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 53966448587597046358883696640,
    2089023816294079213892272128, 55010960495744085965829832704, 55010960495744085965829832704, 2089023816294079213892272128, 1392682544196052809261514752, 1586110675334393477214502912,
    1237940039285380274899124224, 16596133651669629310366384128, 1470053796651389076442710016, 1237940039285380274899124224, 1470053796651389076442710016, 1431368170423720942852112384,
    54082505466280050759655489536, 1431368170423720942852112384, 16596133651669629310366384128, 54082505466280050759655489536, 1392682544196052809261514752, 1431368170423720942852112384,
    1431368170423720942852112384, 1586110675334393477214502912, 28032874136678924960380485632, 102390586199903791005617356800, 28032864691945959221090058240
  ]
def positiveScales : Array ℕ := #[
    13, 14, 9, 14, 9, 7,
    8, 9, 11, 10, 15, 10,
    10, 10, 9, 9, 10, 15,
    10, 7, 11, 4, 8, 9,
    4, 7, 4, 9, 10, 7,
    14, 10, 8, 9, 4, 10,
    4, 9, 9, 4, 3, 5,
    0, 8, 4, 0, 4, 5,
    9, 5, 8, 9, 3, 5,
    5, 5, 16, 23, 21
  ]
def negativeArguments : Array ℕ := #[
    29, 49, 9, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4595233425827331580425549119488, 7764359926397905084167307132928, 1426106925256758076683791106048, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 5, 3, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13166320025266979, 14164042684555913, 9812177305463258, 14410650092641842, 9812177305463258, 7199672344836364,
    8784634845528344, 9862637357422660, 11229419688230416, 10972261847801237, 15778359520105441, 10743992861047947,
    10972261847801237, 10824163209679199, 9862637357422660, 9862637357422660, 10824163209679199, 15778359520105441,
    10824163209679199, 7199672344836364, 11229419688230416, 4754887502147955, 8661778097770205, 9473705749619407,
    4754887502147955, 7813781191164178, 4754887502147955, 9473705749619407, 10464545750333933, 7813781191164178,
    14412503690893657, 10446049406716546, 8661778097770205, 9473705749619407, 4754887502147955, 10446049406716546,
    4754887502147955, 9473705749619407, 9473705749619407, 4754887502147955, 3169925001442312, 5357552004618083,
    0, 8744833837487090, 4247927513443585, 0, 4247927513443585, 5209453365628949,
    9449148645375433, 5209453365628949, 8744833837487090, 9449148645375433, 3169925001442312, 5209453365628949,
    5209453365628949, 5357552004618083, 16501106324518755, 23369997831651245, 21501105838451160
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4857980997143165, 5614709844123661, 3169925001442313, 0, 0
  ]

abbrev PositiveTerm := Fin 59
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 1922491217 / 1000000000000
noncomputable def negativeCeiling : ℝ := 847876657 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 711273923821906304196728061952, coefficient := 711273923821906304196728061952 }, { argument := 710152040661303928322600730624, coefficient := 710152040661303928322600730624 }, { argument := 34778377978673652097947271168, coefficient := 34778377978673652097947271168 }, { argument := 842534253612384281469625827328, coefficient := 842534253612384281469625827328 }, { argument := 34778377978673652097947271168, coefficient := 34778377978673652097947271168 }, { argument := 4595233425827331580425549119488, coefficient := (-4595233425827331580425549119488) }, { argument := 90988592887475450205085630464, coefficient := 90988592887475450205085630464 }, { argument := 68241444665606587653814222848, coefficient := 68241444665606587653814222848 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 92884188572631188751024914432, coefficient := 92884188572631188751024914432 }, { argument := 1243510769462164486136170283008, coefficient := 1243510769462164486136170283008 }, { argument := 2174248250873632112192358711296, coefficient := 2174248250873632112192358711296 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 1243510769462164486136170283008, coefficient := 1243510769462164486136170283008 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 72032636035918064745692790784, coefficient := 72032636035918064745692790784 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 2174248250873632112192358711296, coefficient := 2174248250873632112192358711296 }, { argument := 70137040350762326199753506816, coefficient := 70137040350762326199753506816 }, { argument := 90988592887475450205085630464, coefficient := 90988592887475450205085630464 }, { argument := 92884188572631188751024914432, coefficient := 92884188572631188751024914432 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 843617451146758989210162561024, coefficient := 843617451146758989210162561024 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1586110675334393477214502912, coefficient := 1586110675334393477214502912 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 16596133651669629310366384128, coefficient := 16596133651669629310366384128 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 54082505466280050759655489536, coefficient := 54082505466280050759655489536 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 16596133651669629310366384128, coefficient := 16596133651669629310366384128 }, { argument := 54082505466280050759655489536, coefficient := 54082505466280050759655489536 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1586110675334393477214502912, coefficient := 1586110675334393477214502912 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28032874136678924960380485632, coefficient := 28032874136678924960380485632 }, { argument := 102390586199903791005617356800, coefficient := 102390586199903791005617356800 }, { argument := 28032864691945959221090058240, coefficient := 28032864691945959221090058240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk14
