import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-269637355812832542618098142806016)
def positiveArguments : Array ℕ := #[
    2597, 217, 135, 105, 15, 141,
    1665, 117, 105, 1665, 15, 117,
    117, 117, 117, 117, 135, 141,
    924273, 34727311, 69449369, 1853799, 29223, 4447023,
    182293845, 4447023, 116887, 191377, 16061551, 32123103,
    382753, 25020603, 1503, 128534341, 2421, 75,
    2421, 1617, 25045179, 1503, 9, 2675,
    2445, 2675, 2445
  ]
def positiveCoefficients : Array ℕ := #[
    200933142626508285869564100608, 8394780891403984989159686144, 5222559540735198034730680320, 4061990753905154027012751360, 4642275147320176030871715840, 5454673298101206836274266112,
    64411567669067442428345057280, 144838984596389492163197534208, 4061990753905154027012751360, 64411567669067442428345057280, 4642275147320176030871715840, 4526218268637171630099922944,
    4526218268637171630099922944, 4526218268637171630099922944, 144838984596389492163197534208, 4526218268637171630099922944, 5222559540735198034730680320, 5454673298101206836274266112,
    17459023344885502362393772032, 655980358026361367182729805824, 655930744844092338690114715648, 17508636527154530855008862208, 1104013725831197136638705664, 168003778910003346137168216064,
    1721716687322868519580981002240, 168003778910003346137168216064, 1103966502166368440186568704, 14460037286274305472983990272, 1213576481684822927226947239936, 1213576519463754790184108949504,
    14459999507342442515822280704, 118156456988387693642737778688, 58144496220185204786668240896, 1213972527672275272892439068672, 93657901097184551422836867072, 2901421967075110019294822400,
    93657901097184551422836867072, 62554657610139372015996370944, 118272513867070698043509571584, 58144496220185204786668240896, 2785365088392105618523029504, 206968100318024514709697331200,
    189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480
  ]
def positiveScales : Array ℕ := #[
    11, 7, 7, 6, 3, 7,
    10, 6, 6, 10, 3, 6,
    6, 6, 6, 6, 7, 7,
    19, 25, 26, 20, 14, 22,
    27, 22, 16, 17, 23, 24,
    18, 24, 10, 26, 11, 6,
    11, 10, 24, 10, 3, 11,
    11, 11, 11
  ]
def negativeArguments : Array ℕ := #[
    7, 3, 17, 13, 31, 23,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 475368975085586025561263702016, 1346878762742493739090247155712, 2059932225370872777432142708736, 2456073037942194465399862460416, 1822247737828079764651510857728,
    792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    2, 1, 4, 3, 4, 4,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11342630298678407, 7761551232426566, 7076815597050830, 6714245517659862, 3906890595303263, 7139551352398793,
    10701306461953989, 6870364719426147, 6714245517659862, 10701306461953989, 3906890595303263, 6870364719426147,
    6870364719426147, 6870364719426147, 6870364719426147, 6870364719426147, 7076815597050830, 7139551352398793,
    19817959513871760, 25049567368707645, 26049458250503065, 20822053396060570, 14834816670648375, 22084408435650683,
    27441690609900604, 22084408435650683, 16834754958730758, 17546057929235633, 23937107878590058, 24937107923501506,
    18546054159981947, 24576613223284498, 10553629293916271, 26937578619720189, 11241387363998936, 6228818690495880,
    11241387363998936, 10659103963471994, 24578029586906761, 10553629293916271, 3169925001442312, 11385323176175871,
    11255618749839595, 11385323176175871, 11255618749839595
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 1584962500724866, 4087462841250340, 3700439718214233, 4954196321574415, 4523561956057598,
    2321928094887363
  ]

abbrev PositiveTerm := Fin 45
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 19871389 / 8000000000
noncomputable def negativeCeiling : ℝ := 236202401 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }, { argument := 4642275147320176030871715840, coefficient := 4642275147320176030871715840 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 144838984596389492163197534208, coefficient := 144838984596389492163197534208 }, { argument := 4526218268637171630099922944, coefficient := 4526218268637171630099922944 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 17459023344885502362393772032, coefficient := 17459023344885502362393772032 }, { argument := 655980358026361367182729805824, coefficient := 655980358026361367182729805824 }, { argument := 655930744844092338690114715648, coefficient := 655930744844092338690114715648 }, { argument := 17508636527154530855008862208, coefficient := 17508636527154530855008862208 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 1104013725831197136638705664, coefficient := 1104013725831197136638705664 }, { argument := 168003778910003346137168216064, coefficient := 168003778910003346137168216064 }, { argument := 1721716687322868519580981002240, coefficient := 1721716687322868519580981002240 }, { argument := 168003778910003346137168216064, coefficient := 168003778910003346137168216064 }, { argument := 1103966502166368440186568704, coefficient := 1103966502166368440186568704 }, { argument := 2059932225370872777432142708736, coefficient := (-2059932225370872777432142708736) }, { argument := 14460037286274305472983990272, coefficient := 14460037286274305472983990272 }, { argument := 1213576481684822927226947239936, coefficient := 1213576481684822927226947239936 }, { argument := 1213576519463754790184108949504, coefficient := 1213576519463754790184108949504 }, { argument := 14459999507342442515822280704, coefficient := 14459999507342442515822280704 }, { argument := 2456073037942194465399862460416, coefficient := (-2456073037942194465399862460416) }, { argument := 118156456988387693642737778688, coefficient := 118156456988387693642737778688 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 1213972527672275272892439068672, coefficient := 1213972527672275272892439068672 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 118272513867070698043509571584, coefficient := 118272513867070698043509571584 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 1822247737828079764651510857728, coefficient := (-1822247737828079764651510857728) }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
