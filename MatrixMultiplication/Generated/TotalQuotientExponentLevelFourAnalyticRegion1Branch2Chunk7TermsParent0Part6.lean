import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-28626250638470541992249278706221056)
def positiveArguments : Array ℕ := #[
    17741, 565, 17289, 9831, 17741, 276963,
    339, 1071822051, 17289, 565, 339, 565,
    8701, 9831, 17283451, 331588001, 21965807199, 4305,
    3813, 178473, 48585, 10982905071, 178473, 4305,
    4305, 1845, 4305, 48585, 1845, 165792529,
    3813, 74468891, 80661, 410019813, 129927, 4025,
    129927, 86779, 74633755, 80661, 483, 14445,
    13203, 14445, 13203
  ]
def positiveCoefficients : Array ℕ := #[
    343160847452530179015396294656, 10928689409316247739343831040, 334417895925077180823921229824, 190159195722102710664582660096, 343160847452530179015396294656, 5357243548446824641826345975808,
    209830836658871956595401555968, 20246146116971997994343920041984, 334417895925077180823921229824, 10928689409316247739343831040, 209830836658871956595401555968, 10928689409316247739343831040,
    336603633806940430371789996032, 190159195722102710664582660096, 163237579421439704876598689792, 1565880062044146399988674461696, 103730591685734363013579490197504, 333083241820222630215045611520,
    295016585612197186761897541632, 13808679539461229612629462351872, 3759082300542512540998371901440, 103730605583658922098945354104832, 13808679539461229612629462351872, 333083241820222630215045611520,
    333083241820222630215045611520, 285499921560190825898610524160, 333083241820222630215045611520, 3759082300542512540998371901440, 285499921560190825898610524160, 1565866164119587314622810554368,
    295016585612197186761897541632, 1406677579499491906509596524544, 1560210648574969661775597797376, 15490110577789437071167831670784, 2513153679441118796512789266432, 77854822783182118851077734400,
    2513153679441118796512789266432, 1678549979205406482429235953664, 1409791772410819191263639633920, 1560210648574969661775597797376, 74740629871854834097034625024, 558813870858666189716182794240,
    510766323083902367796660535296, 558813870858666189716182794240, 510766323083902367796660535296
  ]
def positiveScales : Array ℕ := #[
    14, 9, 14, 13, 14, 18,
    8, 29, 14, 9, 8, 9,
    13, 13, 24, 28, 34, 12,
    11, 17, 15, 33, 17, 12,
    12, 10, 12, 15, 10, 27,
    11, 26, 16, 28, 16, 11,
    16, 16, 26, 16, 8, 13,
    13, 13, 13
  ]
def negativeArguments : Array ℕ := #[
    1623, 3133, 357, 27
  ]
def negativeCoefficients : Array ℕ := #[
    257174615521302039828643662790656, 248221833157190169680573196402688, 28284454017592368520895190269952, 2139160387885137115025686659072
  ]
def negativeScales : Array ℕ := #[
    10, 11, 8, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14114799711306814, 9142107057302549, 14077566805107839, 13263122458263915, 14114799711306814, 18079333731282027,
    8405141463136342, 29997418255162832, 14077566805107839, 9142107057302549, 8405141463136342, 9142107057302549,
    13086965503110088, 13263122458263915, 24042887974507971, 28304816560833038, 34354540465404082, 12071797522284206,
    11896710815471615, 17445346309405981, 15568223348403562, 33354540658697739, 17445346309405981, 12071797522284206,
    12071797522284206, 10849405100841772, 12071797522284206, 15568223348403562, 10849405100841772, 27304803756176854,
    11896710815471615, 26150134537127479, 16299583671309825, 28611118384502831, 16987341740200876, 11974773066918090,
    16987341740200876, 16405058340867121, 26153324937546686, 16299583671309825, 8915879378478017, 13818282583394157,
    13688578157112273, 13818282583394157, 13688578157112273
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10664447284578613, 11613329054379197, 8479780264029236, 4754887502413606
  ]

abbrev PositiveTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 27657744523 / 250000000000
noncomputable def negativeCeiling : ℝ := 70721644717 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 343160847452530179015396294656, coefficient := 343160847452530179015396294656 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 190159195722102710664582660096, coefficient := 190159195722102710664582660096 }, { argument := 343160847452530179015396294656, coefficient := 343160847452530179015396294656 }, { argument := 5357243548446824641826345975808, coefficient := 5357243548446824641826345975808 }, { argument := 209830836658871956595401555968, coefficient := 209830836658871956595401555968 }, { argument := 20246146116971997994343920041984, coefficient := 20246146116971997994343920041984 }, { argument := 334417895925077180823921229824, coefficient := 334417895925077180823921229824 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 209830836658871956595401555968, coefficient := 209830836658871956595401555968 }, { argument := 10928689409316247739343831040, coefficient := 10928689409316247739343831040 }, { argument := 336603633806940430371789996032, coefficient := 336603633806940430371789996032 }, { argument := 190159195722102710664582660096, coefficient := 190159195722102710664582660096 }, { argument := 163237579421439704876598689792, coefficient := 163237579421439704876598689792 }, { argument := 257174615521302039828643662790656, coefficient := (-257174615521302039828643662790656) }, { argument := 1565880062044146399988674461696, coefficient := 1565880062044146399988674461696 }, { argument := 103730591685734363013579490197504, coefficient := 103730591685734363013579490197504 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 295016585612197186761897541632, coefficient := 295016585612197186761897541632 }, { argument := 13808679539461229612629462351872, coefficient := 13808679539461229612629462351872 }, { argument := 3759082300542512540998371901440, coefficient := 3759082300542512540998371901440 }, { argument := 103730605583658922098945354104832, coefficient := 103730605583658922098945354104832 }, { argument := 13808679539461229612629462351872, coefficient := 13808679539461229612629462351872 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 285499921560190825898610524160, coefficient := 285499921560190825898610524160 }, { argument := 333083241820222630215045611520, coefficient := 333083241820222630215045611520 }, { argument := 3759082300542512540998371901440, coefficient := 3759082300542512540998371901440 }, { argument := 285499921560190825898610524160, coefficient := 285499921560190825898610524160 }, { argument := 1565866164119587314622810554368, coefficient := 1565866164119587314622810554368 }, { argument := 295016585612197186761897541632, coefficient := 295016585612197186761897541632 }, { argument := 248221833157190169680573196402688, coefficient := (-248221833157190169680573196402688) }, { argument := 1406677579499491906509596524544, coefficient := 1406677579499491906509596524544 }, { argument := 1560210648574969661775597797376, coefficient := 1560210648574969661775597797376 }, { argument := 15490110577789437071167831670784, coefficient := 15490110577789437071167831670784 }, { argument := 2513153679441118796512789266432, coefficient := 2513153679441118796512789266432 }, { argument := 77854822783182118851077734400, coefficient := 77854822783182118851077734400 }, { argument := 2513153679441118796512789266432, coefficient := 2513153679441118796512789266432 }, { argument := 1678549979205406482429235953664, coefficient := 1678549979205406482429235953664 }, { argument := 1409791772410819191263639633920, coefficient := 1409791772410819191263639633920 }, { argument := 1560210648574969661775597797376, coefficient := 1560210648574969661775597797376 }, { argument := 74740629871854834097034625024, coefficient := 74740629871854834097034625024 }, { argument := 28284454017592368520895190269952, coefficient := (-28284454017592368520895190269952) }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }] }

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

end TermShard12


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
