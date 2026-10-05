import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-204284423307074030364292724885028864)
def positiveArguments : Array ℕ := #[
    7239, 105, 1869, 105, 3325, 5677,
    105, 5677, 5677, 1869, 105, 19,
    6882853829, 6882851899, 18523799117, 131207596379, 37047597579, 6128941485,
    113751089771, 227492330963, 3069395413, 105258763, 15641437503, 1071,
    160514733639, 1099, 35, 1071, 609, 1099,
    17157, 21, 7820719079, 1071, 35, 21,
    35, 539, 609, 105254305, 61011835, 5078173829,
    35, 31, 1451, 395, 2539086627, 1451,
    35, 35, 15, 35, 395, 15,
    30506205, 31
  ]
def positiveCoefficients : Array ℕ := #[
    560090496524179238124672516096, 8123981507810308054025502720, 144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864,
    8123981507810308054025502720, 219618300094471994393822756864, 219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 1505335087771022414277335056384,
    65006716457121200933918073683968, 65006698228786577057087548817408, 349904672342124518542260964425728, 1239220710876156453739107941613568, 349904666155824425983025734483968, 57886215688466620794906209157120,
    2148697334897866185576216698814464, 2148604317699119197881038584938496, 57979240084100128383423628705792, 994140908839039090885023236096, 147729200416134951411618127282176, 41432305689832571075530063872,
    1516018796287124715669689349439488, 42515503224207278816066797568, 1353996917968384675670917120, 41432305689832571075530063872, 23559546372649893356673957888, 42515503224207278816066797568,
    663729289188102168013883572224, 25996740824992985772881608704, 147729206602435043970853357223936, 41432305689832571075530063872, 1353996917968384675670917120, 25996740824992985772881608704,
    1353996917968384675670917120, 41703105073426248010664247296, 23559546372649893356673957888, 994098804219477825128297922560, 576240489324746240573120184320, 47961995768510818285412279123968,
    5415987671873538702683668480, 4797017652230848565234106368, 224531374625385847359828656128, 61123289439715651073144258560, 47961990337789362985320283373568, 224531374625385847359828656128,
    5415987671873538702683668480, 5415987671873538702683668480, 4642275147320176030871715840, 5415987671873538702683668480, 61123289439715651073144258560, 4642275147320176030871715840,
    576245920046201540665115934720, 4797017652230848565234106368
  ]
def positiveScales : Array ℕ := #[
    12, 6, 10, 6, 11, 12,
    6, 12, 12, 10, 6, 4,
    32, 32, 34, 36, 35, 32,
    36, 37, 31, 26, 33, 10,
    37, 10, 5, 10, 9, 10,
    14, 4, 32, 10, 5, 4,
    5, 9, 9, 26, 25, 32,
    5, 4, 10, 8, 31, 10,
    5, 5, 3, 5, 8, 3,
    24, 4
  ]
def negativeArguments : Array ℕ := #[
    381, 7, 19, 1641, 12237, 27851,
    11451, 1233
  ]
def negativeCoefficients : Array ℕ := #[
    60371859835869425246280490156032, 1109194275199700726309615304704, 1505335087771022414277335056384, 130013414685907777991005622501376, 1939030049374105398264394640523264, 4413167108369552132635585121615872,
    1814483377901681859567343550595072, 97688324380087928252839690764288
  ]
def negativeScales : Array ℕ := #[
    8, 2, 4, 10, 13, 14,
    13, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12821574700875186, 6714245517659862, 10868050853594526, 6714245517659862, 11699138625271509, 12470913026274870,
    6714245517659862, 12470913026274870, 12470913026274870, 10868050853594526, 6714245517659862, 4247927513443585,
    32680359725781766, 32680359321240004, 34108660965677006, 36933060291748904, 35108660940170217, 32512990784964971,
    36727089410599635, 37727026954918282, 31515307366075420, 26649365104601893, 33864654056207953, 10064742764750255,
    37223914772088871, 10101975670949231, 5129283016944966, 10064742764750255, 9250298417906332, 10101975670949231,
    14066509690924443, 4392317422778759, 32864654116622172, 10064742764750255, 5129283016944966, 4392317422778759,
    5129283016944966, 9074141462752505, 9250298417906332, 26649304001179154, 25862585786090017, 32241662634151671,
    5129283016944966, 4954196309696329, 10502831804066725, 8625708843063759, 31241662470795763, 10502831804066725,
    5129283016944966, 5129283016944966, 3906890595303263, 5129283016944966, 8625708843063759, 3906890595303263,
    24862599382562528, 4954196309696329
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    8573647187496003, 2807354922807594, 4247927513443586, 10680359523558999, 13578962292516804, 14765441508834144,
    13483185971936868, 10267957084402840
  ]

abbrev PositiveTerm := Fin 56
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 115624957309 / 31250000000
noncomputable def negativeCeiling : ℝ := 1430919709219 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 560090496524179238124672516096, coefficient := 560090496524179238124672516096 }, { argument := 60371859835869425246280490156032, coefficient := (-60371859835869425246280490156032) }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1505335087771022414277335056384, coefficient := 1505335087771022414277335056384 }, { argument := 1505335087771022414277335056384, coefficient := (-1505335087771022414277335056384) }, { argument := 65006716457121200933918073683968, coefficient := 65006716457121200933918073683968 }, { argument := 65006698228786577057087548817408, coefficient := 65006698228786577057087548817408 }, { argument := 130013414685907777991005622501376, coefficient := (-130013414685907777991005622501376) }, { argument := 349904672342124518542260964425728, coefficient := 349904672342124518542260964425728 }, { argument := 1239220710876156453739107941613568, coefficient := 1239220710876156453739107941613568 }, { argument := 349904666155824425983025734483968, coefficient := 349904666155824425983025734483968 }, { argument := 1939030049374105398264394640523264, coefficient := (-1939030049374105398264394640523264) }, { argument := 57886215688466620794906209157120, coefficient := 57886215688466620794906209157120 }, { argument := 2148697334897866185576216698814464, coefficient := 2148697334897866185576216698814464 }, { argument := 2148604317699119197881038584938496, coefficient := 2148604317699119197881038584938496 }, { argument := 57979240084100128383423628705792, coefficient := 57979240084100128383423628705792 }, { argument := 4413167108369552132635585121615872, coefficient := (-4413167108369552132635585121615872) }, { argument := 994140908839039090885023236096, coefficient := 994140908839039090885023236096 }, { argument := 147729200416134951411618127282176, coefficient := 147729200416134951411618127282176 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1516018796287124715669689349439488, coefficient := 1516018796287124715669689349439488 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 23559546372649893356673957888, coefficient := 23559546372649893356673957888 }, { argument := 42515503224207278816066797568, coefficient := 42515503224207278816066797568 }, { argument := 663729289188102168013883572224, coefficient := 663729289188102168013883572224 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 147729206602435043970853357223936, coefficient := 147729206602435043970853357223936 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 41703105073426248010664247296, coefficient := 41703105073426248010664247296 }, { argument := 23559546372649893356673957888, coefficient := 23559546372649893356673957888 }, { argument := 994098804219477825128297922560, coefficient := 994098804219477825128297922560 }, { argument := 1814483377901681859567343550595072, coefficient := (-1814483377901681859567343550595072) }, { argument := 576240489324746240573120184320, coefficient := 576240489324746240573120184320 }, { argument := 47961995768510818285412279123968, coefficient := 47961995768510818285412279123968 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 47961990337789362985320283373568, coefficient := 47961990337789362985320283373568 }, { argument := 224531374625385847359828656128, coefficient := 224531374625385847359828656128 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 61123289439715651073144258560, coefficient := 61123289439715651073144258560 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 576245920046201540665115934720, coefficient := 576245920046201540665115934720 }, { argument := 4797017652230848565234106368, coefficient := 4797017652230848565234106368 }, { argument := 97688324380087928252839690764288, coefficient := (-97688324380087928252839690764288) }] }

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


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12850650075990580480250470203392)
def positiveArguments : Array ℕ := #[
    10049613, 48670643, 10049613
  ]
def positiveCoefficients : Array ℕ := #[
    47457955597011063844947099648, 459681226405828235464913453056, 47457955597011063844947099648
  ]
def positiveScales : Array ℕ := #[
    23, 25, 23
  ]
def negativeArguments : Array ℕ := #[
    7
  ]
def negativeCoefficients : Array ℕ := #[
    554597137599850363154807652352
  ]
def negativeScales : Array ℕ := #[
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23260636610020625, 25536548498757699, 23260636610020625
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 167874603 / 1000000000000
noncomputable def negativeCeiling : ℝ := 18741117 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 47457955597011063844947099648, coefficient := 47457955597011063844947099648 }, { argument := 459681226405828235464913453056, coefficient := 459681226405828235464913453056 }, { argument := 47457955597011063844947099648, coefficient := 47457955597011063844947099648 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
