import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9

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
def constantNumerator : ℤ := (-13395326255633953421940597194752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8361903321, 328787932063, 4162841, 2890337288467, 3673095, 1224365,
    32568109, 4162841, 3673095, 593327279, 3673095, 328290507779,
    32568109, 1224365, 3673095, 1224365, 4162841, 4162841,
    16722787737, 8361903321, 76168916913, 304705713687, 2083021203, 76168916913,
    3185371273223, 17305439, 29005122435675, 15269505, 5089835, 135389611,
    17305439, 15269505, 2466534041, 15269505, 3181242604491, 135389611,
    5089835, 15269505, 5089835, 17305439, 17305439, 152327602801,
    328787932063, 3185371273223, 12743527407089, 81690760085, 4162841, 17305439,
    17305439, 4162807, 304705713687, 12743527407089, 17305439, 116042977456957,
    15269505, 5089835, 135389611, 17305439, 15269505, 2466534041,
    15269505, 12727012763981, 135389611, 5089835
  ]
def negativeCoefficients : Array ℕ := #[
    9414666170140928249954304, 185091151040355344272326656, 38395431273272571779350528, 1627115241914378875729608704, 33878321711711092746485760, 5646386951951848791080960,
    37548473230479794460688384, 38395431273272571779350528, 33878321711711092746485760, 684059779228966481039458304, 33878321711711092746485760, 184811126062846914800386048,
    37548473230479794460688384, 5646386951951848791080960, 33878321711711092746485760, 5646386951951848791080960, 38395431273272571779350528, 38395431273272571779350528,
    9414092577618637508050944, 9414666170140928249954304, 343034305826601070491598848, 343068134654608560711794688, 9381093513635642304626688, 343034305826601070491598848,
    7172818439561892601532514304, 1276916017264768596832157696, 65313729296570771667576422400, 1126690603468913467793080320, 187781767244818911298846720, 1248748752178045760137330688,
    1276916017264768596832157696, 1126690603468913467793080320, 22749761101709811103855280128, 1126690603468913467793080320, 7163521504080406892425248768, 1248748752178045760137330688,
    187781767244818911298846720, 1126690603468913467793080320, 187781767244818911298846720, 1276916017264768596832157696, 1276916017264768596832157696, 343011267606412261377179648,
    185091151040355344272326656, 7172818439561892601532514304, 7173968160243965435752480768, 183951238339209294071726080, 38395431273272571779350528, 1276916017264768596832157696,
    1276916017264768596832157696, 38395117678623318716973056, 343068134654608560711794688, 7173968160243965435752480768, 1276916017264768596832157696, 65326388754264301591366467584,
    1126690603468913467793080320, 187781767244818911298846720, 1248748752178045760137330688, 1276916017264768596832157696, 1126690603468913467793080320, 22749761101709811103855280128,
    1126690603468913467793080320, 7164671242675547244511363072, 1248748752178045760137330688, 187781767244818911298846720
  ]
def negativeScales : Array ℕ := #[
    32, 38, 21, 41, 21, 20,
    24, 21, 21, 29, 21, 38,
    24, 20, 21, 20, 21, 21,
    33, 32, 36, 38, 30, 36,
    41, 24, 44, 23, 22, 27,
    24, 23, 31, 23, 41, 27,
    22, 23, 22, 24, 24, 37,
    38, 41, 43, 36, 21, 24,
    24, 21, 38, 43, 24, 46,
    23, 22, 27, 24, 23, 31,
    23, 43, 27, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32961184229828897, 38258366390613985, 21989137044907655, 41394374996774096, 21808564780144423, 20223602278654750,
    24956956630986367, 21989137044907655, 21808564780144423, 29144252873218734, 21808564780144423, 38256182080061944,
    24956956630986367, 20223602278654750, 21808564780144423, 20223602278654750, 21989137044907655, 21989137044907655,
    33961096330326644, 32961184229828897, 36148483330265466, 38148625596724716, 30956030390119252, 36148483330265466,
    41534598675281716, 24044722204102048, 44721372942858217, 23864149960723957, 22279187457739071, 27012541798352898,
    24044722204102048, 23864149960723957, 31199838052303055, 23864149960723957, 41532727535974497, 27012541798352898,
    22279187457739071, 23864149960723957, 22279187457739071, 24044722204102048, 24044722204102048, 37148386435460465,
    38258366390613985, 41534598675281716, 43534829904249749, 36249453855477024, 21989137044907655, 24044722204102048,
    24044722204102048, 21989125261645347, 38148625596724716, 43534829904249749, 24044722204102048, 46721652546661613,
    23864149960723957, 22279187457739071, 27012541798352898, 24044722204102048, 23864149960723957, 31199838052303055,
    23864149960723957, 43532959068618208, 27012541798352898, 22279187457739071
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
noncomputable def negativeCeiling : ℝ := 120402031 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9414666170140928249954304, coefficient := (-9414666170140928249954304) }, { argument := 185091151040355344272326656, coefficient := (-185091151040355344272326656) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1627115241914378875729608704, coefficient := (-1627115241914378875729608704) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 37548473230479794460688384, coefficient := (-37548473230479794460688384) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 684059779228966481039458304, coefficient := (-684059779228966481039458304) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 184811126062846914800386048, coefficient := (-184811126062846914800386048) }, { argument := 37548473230479794460688384, coefficient := (-37548473230479794460688384) }, { argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 9414092577618637508050944, coefficient := (-9414092577618637508050944) }, { argument := 9414666170140928249954304, coefficient := (-9414666170140928249954304) }, { argument := 343034305826601070491598848, coefficient := (-343034305826601070491598848) }, { argument := 343068134654608560711794688, coefficient := (-343068134654608560711794688) }, { argument := 9381093513635642304626688, coefficient := (-9381093513635642304626688) }, { argument := 343034305826601070491598848, coefficient := (-343034305826601070491598848) }, { argument := 7172818439561892601532514304, coefficient := (-7172818439561892601532514304) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 65313729296570771667576422400, coefficient := (-65313729296570771667576422400) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 22749761101709811103855280128, coefficient := (-22749761101709811103855280128) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 7163521504080406892425248768, coefficient := (-7163521504080406892425248768) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 343011267606412261377179648, coefficient := (-343011267606412261377179648) }, { argument := 185091151040355344272326656, coefficient := (-185091151040355344272326656) }, { argument := 7172818439561892601532514304, coefficient := (-7172818439561892601532514304) }, { argument := 7173968160243965435752480768, coefficient := (-7173968160243965435752480768) }, { argument := 183951238339209294071726080, coefficient := (-183951238339209294071726080) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 343068134654608560711794688, coefficient := (-343068134654608560711794688) }, { argument := 7173968160243965435752480768, coefficient := (-7173968160243965435752480768) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 65326388754264301591366467584, coefficient := (-65326388754264301591366467584) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 22749761101709811103855280128, coefficient := (-22749761101709811103855280128) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 7164671242675547244511363072, coefficient := (-7164671242675547244511363072) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11797426725256565114737984012288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15269505, 5089835, 17305439, 17305439, 609370495319, 2890337288467,
    29005122435675, 116042977456957, 717011843217, 3673095, 15269505, 15269505,
    3673065, 1224365, 5089835, 5089835, 1224355, 32568109,
    135389611, 135389611, 32567843, 4162841, 17305439, 17305439,
    4162807, 3673095, 15269505, 15269505, 3673065, 593327279,
    2466534041, 2466534041, 593322433, 3673095, 15269505, 15269505,
    3673065, 2083021203, 81690760085, 4162807, 717011843217, 3673065,
    1224355, 32567843, 4162807, 3673065, 593322433, 3673065,
    81566397153, 32567843, 1224355, 3673065, 1224355, 4162807,
    4162807, 4165789651, 328290507779, 3181242604491, 12727012763981, 81566397153,
    32568109, 135389611, 135389611, 32567843
  ]
def negativeCoefficients : Array ℕ := #[
    1126690603468913467793080320, 187781767244818911298846720, 1276916017264768596832157696, 1276916017264768596832157696, 343045091956152872130838528, 1627115241914378875729608704,
    65313729296570771667576422400, 65326388754264301591366467584, 1614567134966156849961762816, 33878321711711092746485760, 1126690603468913467793080320, 1126690603468913467793080320,
    33878045010549987103211520, 5646386951951848791080960, 187781767244818911298846720, 187781767244818911298846720, 5646340835091664517201920, 37548473230479794460688384,
    1248748752178045760137330688, 1248748752178045760137330688, 37548166553359569039392768, 38395431273272571779350528, 1276916017264768596832157696, 1276916017264768596832157696,
    38395117678623318716973056, 33878321711711092746485760, 1126690603468913467793080320, 1126690603468913467793080320, 33878045010549987103211520, 684059779228966481039458304,
    22749761101709811103855280128, 22749761101709811103855280128, 684054192171355156259012608, 33878321711711092746485760, 1126690603468913467793080320, 1126690603468913467793080320,
    33878045010549987103211520, 9381093513635642304626688, 183951238339209294071726080, 38395117678623318716973056, 1614567134966156849961762816, 33878045010549987103211520,
    5646340835091664517201920, 37548166553359569039392768, 38395117678623318716973056, 33878045010549987103211520, 684054192171355156259012608, 33878045010549987103211520,
    183671197912102342905298944, 37548166553359569039392768, 5646340835091664517201920, 33878045010549987103211520, 5646340835091664517201920, 38395117678623318716973056,
    38395117678623318716973056, 9380524359973734289768448, 184811126062846914800386048, 7163521504080406892425248768, 7164671242675547244511363072, 183671197912102342905298944,
    37548473230479794460688384, 1248748752178045760137330688, 1248748752178045760137330688, 37548166553359569039392768
  ]
def negativeScales : Array ℕ := #[
    23, 22, 24, 24, 39, 41,
    44, 46, 39, 21, 23, 23,
    21, 20, 22, 22, 20, 24,
    27, 27, 24, 21, 24, 24,
    21, 21, 23, 23, 21, 29,
    31, 31, 29, 21, 23, 23,
    21, 30, 36, 21, 39, 21,
    20, 24, 21, 21, 29, 21,
    36, 24, 20, 21, 20, 21,
    21, 31, 38, 41, 43, 36,
    24, 27, 27, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23864149960723957, 22279187457739071, 24044722204102048, 24044722204102048, 39148528692640918, 41394374996774096,
    44721372942858217, 46721652546661613, 39383205992547756, 21808564780144423, 23864149960723957, 23864149960723957,
    21808552996885714, 20223602278654750, 22279187457739071, 22279187457739071, 20223590495396224, 24956956630986367,
    27012541798352898, 27012541798352898, 24956944847725528, 21989137044907655, 24044722204102048, 24044722204102048,
    21989125261645347, 21808564780144423, 23864149960723957, 23864149960723957, 21808552996885714, 29144252873218734,
    31199838052303055, 31199838052303055, 29144241089960208, 21808564780144423, 23864149960723957, 23864149960723957,
    21808552996885714, 30956030390119252, 36249453855477024, 21989125261645347, 39383205992547756, 21808552996885714,
    20223590495396224, 24956944847725528, 21989125261645347, 21808552996885714, 29144241089960208, 21808552996885714,
    36247255877477083, 24956944847725528, 20223590495396224, 21808552996885714, 20223590495396224, 21989125261645347,
    21989125261645347, 31955942858720835, 38256182080061944, 41532727535974497, 43532959068618208, 36247255877477083,
    24956956630986367, 27012541798352898, 27012541798352898, 24956944847725528
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
noncomputable def negativeCeiling : ℝ := 52810409 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 343045091956152872130838528, coefficient := (-343045091956152872130838528) }, { argument := 1627115241914378875729608704, coefficient := (-1627115241914378875729608704) }, { argument := 65313729296570771667576422400, coefficient := (-65313729296570771667576422400) }, { argument := 65326388754264301591366467584, coefficient := (-65326388754264301591366467584) }, { argument := 1614567134966156849961762816, coefficient := (-1614567134966156849961762816) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 5646386951951848791080960, coefficient := (-5646386951951848791080960) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 187781767244818911298846720, coefficient := (-187781767244818911298846720) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 37548473230479794460688384, coefficient := (-37548473230479794460688384) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 37548166553359569039392768, coefficient := (-37548166553359569039392768) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 684059779228966481039458304, coefficient := (-684059779228966481039458304) }, { argument := 22749761101709811103855280128, coefficient := (-22749761101709811103855280128) }, { argument := 22749761101709811103855280128, coefficient := (-22749761101709811103855280128) }, { argument := 684054192171355156259012608, coefficient := (-684054192171355156259012608) }, { argument := 33878321711711092746485760, coefficient := (-33878321711711092746485760) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 1126690603468913467793080320, coefficient := (-1126690603468913467793080320) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 9381093513635642304626688, coefficient := (-9381093513635642304626688) }, { argument := 183951238339209294071726080, coefficient := (-183951238339209294071726080) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 1614567134966156849961762816, coefficient := (-1614567134966156849961762816) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 37548166553359569039392768, coefficient := (-37548166553359569039392768) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 684054192171355156259012608, coefficient := (-684054192171355156259012608) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 183671197912102342905298944, coefficient := (-183671197912102342905298944) }, { argument := 37548166553359569039392768, coefficient := (-37548166553359569039392768) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 33878045010549987103211520, coefficient := (-33878045010549987103211520) }, { argument := 5646340835091664517201920, coefficient := (-5646340835091664517201920) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 9380524359973734289768448, coefficient := (-9380524359973734289768448) }, { argument := 184811126062846914800386048, coefficient := (-184811126062846914800386048) }, { argument := 7163521504080406892425248768, coefficient := (-7163521504080406892425248768) }, { argument := 7164671242675547244511363072, coefficient := (-7164671242675547244511363072) }, { argument := 183671197912102342905298944, coefficient := (-183671197912102342905298944) }, { argument := 37548473230479794460688384, coefficient := (-37548473230479794460688384) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 1248748752178045760137330688, coefficient := (-1248748752178045760137330688) }, { argument := 37548166553359569039392768, coefficient := (-37548166553359569039392768) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9
