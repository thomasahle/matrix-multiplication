import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12

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
def constantNumerator : ℤ := (-221667609365884384870085980848128)
def positiveArguments : Array ℕ := #[
    1175, 1, 489, 535, 489, 535,
    9, 1503, 39, 1617, 2421, 75,
    2421, 2523, 1503, 75, 37, 9755948979,
    9755953229, 1762928065, 6372427545, 881600915
  ]
def positiveCoefficients : Array ℕ := #[
    186186181908521193344828283289600, 158456325028528675187087900672, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240,
    2785365088392105618523029504, 58144496220185204786668240896, 3017478845758114420066615296, 62554657610139372015996370944, 93657901097184551422836867072, 2901421967075110019294822400,
    93657901097184551422836867072, 97603834972406701049077825536, 58144496220185204786668240896, 2901421967075110019294822400, 93806144416888975710756037197824, 92142332934031872425299456032768,
    92142373074146976817283772448768, 16650384811732478567635201556480, 60185876506046595608267603312640, 16652970449052844184479056527360
  ]
def positiveScales : Array ℕ := #[
    10, 0, 8, 9, 8, 9,
    3, 10, 5, 10, 11, 6,
    11, 11, 10, 6, 5, 33,
    33, 30, 32, 29
  ]
def negativeArguments : Array ℕ := #[
    1760200157, 1503, 39, 49752503, 2421, 1760485027,
    2421, 2523, 1503, 75, 40917826369939031, 4487904745,
    40917844141013417, 4487904745, 1766245797, 4487904745, 4487905815, 1503,
    39, 40917844241676713, 4487905815, 40917862012757591, 4487905815, 3194890585,
    2421, 1766533033, 4487904745, 4487905815, 2421, 2523,
    1503, 75, 1, 1, 3, 37,
    1163, 295
  ]
def negativeCoefficients : Array ℕ := #[
    8312310224558687315681997750272, 29072248110092602393334120448, 1508739422879057210033307648, 30073542733577148429228272779264, 46828950548592275711418433536, 8313655485098662391514023329792,
    46828950548592275711418433536, 48801917486203350524538912768, 29072248110092602393334120448, 1450710983537555009647411200, 23034688449058509377887296028672, 10348403782275215806158602240,
    23034698453284007223258045743104, 10348403782275215806158602240, 8340859952262183357571726835712, 10348403782275215806158602240, 10348406249527235664811130880, 29072248110092602393334120448,
    1508739422879057210033307648, 23034698509952405017693788307456, 10348406249527235664811130880, 23034708514181557534162149179392, 10348406249527235664811130880, 30174888430079586551055326904320,
    46828950548592275711418433536, 8342216385921256902984328019968, 10348403782275215806158602240, 10348406249527235664811130880, 46828950548592275711418433536, 48801917486203350524538912768,
    29072248110092602393334120448, 1450710983537555009647411200, 158456325028528675187087900672, 158456325028528675187087900672, 475368975085586025561263702016, 93806144416888975710756037197824,
    184284706008178849242583228481536, 93489231766831918360381861396480
  ]
def negativeScales : Array ℕ := #[
    30, 10, 5, 25, 11, 30,
    11, 11, 10, 6, 55, 32,
    55, 32, 30, 32, 32, 10,
    5, 55, 32, 55, 32, 31,
    11, 30, 32, 32, 11, 11,
    10, 6, 0, 0, 1, 5,
    10, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10198445041452361, 0, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509,
    3169925001442312, 10553629293916271, 5285402218862248, 10659103963471994, 11241387363998936, 6228818690495880,
    11241387363998936, 11300924490976300, 10553629293916271, 6228818690495880, 5209453365628949, 33183635067231453,
    33183635695714914, 30715326461715036, 32569195918771300, 29715550480353240
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30713092344931427, 10553629293917849, 5285402218862249, 25568265772279184, 11241387363998937, 30713325811155556,
    11241387363998937, 11300924490976301, 10553629293917849, 6228818690495881, 55183579026707232, 32063394909305849,
    55183579653285856, 32063394909305849, 30718038981588564, 32063394909305849, 32063395253271150, 10553629293917849,
    5285402218862249, 55183579656835076, 32063395253271150, 55183580283413654, 32063395253271150, 31573119378218810,
    11241387363998937, 30718273581021285, 32063394909305849, 32063395253271150, 11241387363998937, 11300924490976301,
    10553629293917849, 6228818690495881, 0, 0, 1584962500724866, 5209453365628950,
    10183635381473219, 8204571144249204
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 3453371313 / 25000000000
noncomputable def negativeCeiling : ℝ := 132041590717 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8312310224558687315681997750272, coefficient := (-8312310224558687315681997750272) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 30073542733577148429228272779264, coefficient := (-30073542733577148429228272779264) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 8313655485098662391514023329792, coefficient := (-8313655485098662391514023329792) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 23034688449058509377887296028672, coefficient := (-23034688449058509377887296028672) }, { argument := 10348403782275215806158602240, coefficient := (-10348403782275215806158602240) }, { argument := 23034698453284007223258045743104, coefficient := (-23034698453284007223258045743104) }, { argument := 10348403782275215806158602240, coefficient := (-10348403782275215806158602240) }, { argument := 8340859952262183357571726835712, coefficient := (-8340859952262183357571726835712) }, { argument := 10348403782275215806158602240, coefficient := (-10348403782275215806158602240) }, { argument := 10348406249527235664811130880, coefficient := (-10348406249527235664811130880) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1508739422879057210033307648, coefficient := (-1508739422879057210033307648) }, { argument := 23034698509952405017693788307456, coefficient := (-23034698509952405017693788307456) }, { argument := 10348406249527235664811130880, coefficient := (-10348406249527235664811130880) }, { argument := 23034708514181557534162149179392, coefficient := (-23034708514181557534162149179392) }, { argument := 10348406249527235664811130880, coefficient := (-10348406249527235664811130880) }, { argument := 30174888430079586551055326904320, coefficient := (-30174888430079586551055326904320) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 8342216385921256902984328019968, coefficient := (-8342216385921256902984328019968) }, { argument := 10348403782275215806158602240, coefficient := (-10348403782275215806158602240) }, { argument := 10348406249527235664811130880, coefficient := (-10348406249527235664811130880) }, { argument := 46828950548592275711418433536, coefficient := (-46828950548592275711418433536) }, { argument := 48801917486203350524538912768, coefficient := (-48801917486203350524538912768) }, { argument := 29072248110092602393334120448, coefficient := (-29072248110092602393334120448) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 186186181908521193344828283289600, coefficient := 186186181908521193344828283289600 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 3017478845758114420066615296, coefficient := 3017478845758114420066615296 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 97603834972406701049077825536, coefficient := 97603834972406701049077825536 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 93806144416888975710756037197824, coefficient := 93806144416888975710756037197824 }, { argument := 93806144416888975710756037197824, coefficient := (-93806144416888975710756037197824) }, { argument := 92142332934031872425299456032768, coefficient := 92142332934031872425299456032768 }, { argument := 92142373074146976817283772448768, coefficient := 92142373074146976817283772448768 }, { argument := 184284706008178849242583228481536, coefficient := (-184284706008178849242583228481536) }, { argument := 16650384811732478567635201556480, coefficient := 16650384811732478567635201556480 }, { argument := 60185876506046595608267603312640, coefficient := 60185876506046595608267603312640 }, { argument := 16652970449052844184479056527360, coefficient := 16652970449052844184479056527360 }, { argument := 93489231766831918360381861396480, coefficient := (-93489231766831918360381861396480) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk12
