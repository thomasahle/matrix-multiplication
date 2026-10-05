import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 20, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2646493832964880145677107656130560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    135838880507, 3625921797, 324802457655, 590688276425, 324802457655, 3217764391,
    182458201, 3217764391, 182458201, 9776662605, 17779914675, 9776662605,
    11557, 11557, 750551, 2025877630551, 10234990167, 54948074784969,
    161066424207, 4848153237, 439584297650079, 4848153237, 4848153237, 415325127303,
    4848153237, 161066424207, 415325127303, 16207321674081, 4848153237, 4848153237,
    10234990167, 3528722719136801, 5453818095, 306394275, 12871797700116347, 16565717135,
    882180390861081, 16565717135, 16565717135, 5453818095, 306394275, 18328015021,
    1901731315, 18328015021, 1901731315, 9776662605, 17779914675, 9776662605,
    381, 381, 17009705, 889, 889, 15,
    17295229, 1277207407, 13312119205, 1277207407, 17295229, 1807823619,
    67924577533, 135838880507, 3625921797, 9776662605
  ]
def negativeCoefficients : Array ℕ := #[
    626446265992960545547593187328, 16721612855136009462887743488, 374471738179604302345304801280, 1362034432819072275014326681600, 374471738179604302345304801280, 237429104841091497866165223424,
    13463038951985824737488011264, 237429104841091497866165223424, 13463038951985824737488011264, 45086898242360384228866129920, 163990767831058869232494182400, 45086898242360384228866129920,
    223544891156580309953268416512, 223544891156580309953268416512, 3544376886084295084784746496, 145979867872763311409369972736, 47200561051895696000934739968, 3959426066021000568353517993984,
    371393888276758239586302296064, 44716320996532764632464490496, 3959423358189633969725393338368, 44716320996532764632464490496, 44716320996532764632464490496, 1915349082684820085090562342912,
    44716320996532764632464490496, 371393888276758239586302296064, 1915349082684820085090562342912, 145982575704129910037494628352, 44716320996532764632464490496, 44716320996532764632464490496,
    47200561051895696000934739968, 3972988580749575099530633805824, 402420746492124665510709166080, 22607907106299138511837593600, 14492355831458096941626218774528, 611167088773620044436676280320,
    3972987279555522906509254066176, 611167088773620044436676280320, 611167088773620044436676280320, 402420746492124665510709166080, 22607907106299138511837593600, 1352368809885965572836891295744,
    140323003459056490091024220160, 1352368809885965572836891295744, 140323003459056490091024220160, 45086898242360384228866129920, 163990767831058869232494182400, 45086898242360384228866129920,
    117913788741932471184141582336, 117913788741932471184141582336, 80326060775500218539630919680, 8597880429099242690510323712, 8597880429099242690510323712, 2321137573660088015435857920,
    79760165764799893671510016, 11780159082987596645302009856, 122782628026674428829646192640, 11780159082987596645302009856, 79760165764799893671510016, 16674229815050202178652209152,
    626493649033046352831828721664, 626446265992960545547593187328, 16721612855136009462887743488, 45086898242360384228866129920
  ]
def negativeScales : Array ℕ := #[
    36, 31, 38, 39, 38, 31,
    27, 31, 27, 33, 34, 33,
    13, 13, 19, 40, 33, 45,
    37, 32, 48, 32, 32, 38,
    32, 37, 38, 43, 32, 32,
    33, 51, 32, 28, 53, 33,
    49, 33, 33, 32, 28, 34,
    30, 34, 30, 33, 34, 33,
    8, 8, 24, 9, 9, 3,
    24, 30, 33, 30, 24, 30,
    35, 36, 31, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36983105536126887, 31755700663962484, 38240771592642654, 39103606022385978, 38240771592642654, 31583411547863479,
    27442990756697836, 31583411547863479, 27442990756697836, 33186694919886862, 34049529349630186, 33186694919886862,
    13496479326971103, 13496479326971103, 19517590580856519, 40881684175185869, 33252790665203961, 45643134167924908,
    37228864825958480, 32174788153202688, 48643133181272763, 32174788153202688, 32174788153202688, 38595450201680393,
    32174788153202688, 37228864825958480, 38595450201680393, 43881710935991546, 32174788153202688, 32174788153202688,
    33252790665203961, 51648067493447574, 32344619435827644, 28190814099748608, 53515063075402974, 33947481618346792,
    49648067020950239, 33947481618346792, 33947481618346792, 32344619435827644, 28190814099748608, 34093331495011724,
    30824666285314204, 34093331495011724, 30824666285314204, 33186694919886862, 34049529349630186, 33186694919886862,
    8573647187496003, 8573647187496003, 24019854784711506, 9796039609425563, 9796039609425563, 3906890600547867,
    24043870780262774, 30250345678755404, 33632021206325742, 30250345678755404, 24043870780262774, 30751606781747137,
    35983214654363482, 36983105536126887, 31755700663962484, 33186694919886862
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
noncomputable def negativeCeiling : ℝ := 6449474173 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 626446265992960545547593187328, coefficient := (-626446265992960545547593187328) }, { argument := 16721612855136009462887743488, coefficient := (-16721612855136009462887743488) }, { argument := 374471738179604302345304801280, coefficient := (-374471738179604302345304801280) }, { argument := 1362034432819072275014326681600, coefficient := (-1362034432819072275014326681600) }, { argument := 374471738179604302345304801280, coefficient := (-374471738179604302345304801280) }, { argument := 237429104841091497866165223424, coefficient := (-237429104841091497866165223424) }, { argument := 13463038951985824737488011264, coefficient := (-13463038951985824737488011264) }, { argument := 237429104841091497866165223424, coefficient := (-237429104841091497866165223424) }, { argument := 13463038951985824737488011264, coefficient := (-13463038951985824737488011264) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 3544376886084295084784746496, coefficient := (-3544376886084295084784746496) }, { argument := 145979867872763311409369972736, coefficient := (-145979867872763311409369972736) }, { argument := 47200561051895696000934739968, coefficient := (-47200561051895696000934739968) }, { argument := 3959426066021000568353517993984, coefficient := (-3959426066021000568353517993984) }, { argument := 371393888276758239586302296064, coefficient := (-371393888276758239586302296064) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 3959423358189633969725393338368, coefficient := (-3959423358189633969725393338368) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 1915349082684820085090562342912, coefficient := (-1915349082684820085090562342912) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 371393888276758239586302296064, coefficient := (-371393888276758239586302296064) }, { argument := 1915349082684820085090562342912, coefficient := (-1915349082684820085090562342912) }, { argument := 145982575704129910037494628352, coefficient := (-145982575704129910037494628352) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 47200561051895696000934739968, coefficient := (-47200561051895696000934739968) }, { argument := 3972988580749575099530633805824, coefficient := (-3972988580749575099530633805824) }, { argument := 402420746492124665510709166080, coefficient := (-402420746492124665510709166080) }, { argument := 22607907106299138511837593600, coefficient := (-22607907106299138511837593600) }, { argument := 14492355831458096941626218774528, coefficient := (-14492355831458096941626218774528) }, { argument := 611167088773620044436676280320, coefficient := (-611167088773620044436676280320) }, { argument := 3972987279555522906509254066176, coefficient := (-3972987279555522906509254066176) }, { argument := 611167088773620044436676280320, coefficient := (-611167088773620044436676280320) }, { argument := 611167088773620044436676280320, coefficient := (-611167088773620044436676280320) }, { argument := 402420746492124665510709166080, coefficient := (-402420746492124665510709166080) }, { argument := 22607907106299138511837593600, coefficient := (-22607907106299138511837593600) }, { argument := 1352368809885965572836891295744, coefficient := (-1352368809885965572836891295744) }, { argument := 140323003459056490091024220160, coefficient := (-140323003459056490091024220160) }, { argument := 1352368809885965572836891295744, coefficient := (-1352368809885965572836891295744) }, { argument := 140323003459056490091024220160, coefficient := (-140323003459056490091024220160) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 80326060775500218539630919680, coefficient := (-80326060775500218539630919680) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 2321137573660088015435857920, coefficient := (-2321137573660088015435857920) }, { argument := 79760165764799893671510016, coefficient := (-79760165764799893671510016) }, { argument := 11780159082987596645302009856, coefficient := (-11780159082987596645302009856) }, { argument := 122782628026674428829646192640, coefficient := (-122782628026674428829646192640) }, { argument := 11780159082987596645302009856, coefficient := (-11780159082987596645302009856) }, { argument := 79760165764799893671510016, coefficient := (-79760165764799893671510016) }, { argument := 16674229815050202178652209152, coefficient := (-16674229815050202178652209152) }, { argument := 626493649033046352831828721664, coefficient := (-626493649033046352831828721664) }, { argument := 626446265992960545547593187328, coefficient := (-626446265992960545547593187328) }, { argument := 16721612855136009462887743488, coefficient := (-16721612855136009462887743488) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }] }

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

end TermShard2


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2388740658491724617636866473066496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17779914675, 9776662605, 1807823619, 67924577533, 135838880507, 3625921797,
    837534096495, 1523146023825, 837534096495, 11557, 11557, 9776662605,
    17779914675, 9776662605, 11557, 11557, 141, 595177443,
    22362345501, 44721308379, 1193737509, 324802457655, 590688276425, 324802457655,
    381, 381, 837534096495, 1523146023825, 837534096495, 142621,
    142621, 1665, 5715, 5715, 117, 130270418167775,
    145577745, 8178525, 474730802460805, 442185585, 32567596718055, 442185585,
    442185585, 145577745, 8178525, 3217764391, 182458201, 3217764391,
    182458201, 8504853, 11557, 11557, 1665, 15,
    33436935, 1256311545, 2512433055, 67063905, 9776662605, 17779914675,
    9776662605, 889, 889, 9776662605
  ]
def negativeCoefficients : Array ℕ := #[
    163990767831058869232494182400, 45086898242360384228866129920, 16674229815050202178652209152, 626493649033046352831828721664, 626446265992960545547593187328, 16721612855136009462887743488,
    1931222141381103124469765898240, 7024271222097021565458500812800, 1931222141381103124469765898240, 223544891156580309953268416512, 223544891156580309953268416512, 45086898242360384228866129920,
    163990767831058869232494182400, 45086898242360384228866129920, 223544891156580309953268416512, 223544891156580309953268416512, 2727336649050603418137133056, 10979085969465854455487397888,
    412512464344817203960784879616, 412481265154427782148476895232, 11010285159855276267795382272, 374471738179604302345304801280, 1362034432819072275014326681600, 374471738179604302345304801280,
    117913788741932471184141582336, 117913788741932471184141582336, 1931222141381103124469765898240, 7024271222097021565458500812800, 1931222141381103124469765898240, 2758691349108128440412312436736,
    2758691349108128440412312436736, 32205783834533721214172528640, 221088353891123383470265466880, 221088353891123383470265466880, 72419492298194746081598767104, 146671451679447545567353241600,
    10741741619371001236873543680, 603468630301741642520985600, 534499366265944485877063352320, 16313768639157082402817310720, 146671416443785086479137505280, 16313768639157082402817310720,
    16313768639157082402817310720, 10741741619371001236873543680, 603468630301741642520985600, 237429104841091497866165223424, 13463038951985824737488011264, 237429104841091497866165223424,
    13463038951985824737488011264, 80326065497866701409276133376, 223544891156580309953268416512, 223544891156580309953268416512, 32205783834533721214172528640, 2321137573660088015435857920,
    616802582554261486263336960, 23174857547461640671954206720, 23173104783956616974633533440, 618555346059285183584010240, 45086898242360384228866129920, 163990767831058869232494182400,
    45086898242360384228866129920, 8597880429099242690510323712, 8597880429099242690510323712, 45086898242360384228866129920
  ]
def negativeScales : Array ℕ := #[
    34, 33, 30, 35, 36, 31,
    39, 40, 39, 13, 13, 33,
    34, 33, 13, 13, 7, 29,
    34, 35, 30, 38, 39, 38,
    8, 8, 39, 40, 39, 17,
    17, 10, 12, 12, 6, 46,
    27, 22, 48, 28, 44, 28,
    28, 27, 22, 31, 27, 31,
    27, 23, 13, 13, 10, 3,
    24, 30, 31, 25, 33, 34,
    33, 9, 9, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34049529349630186, 33186694919886862, 30751606781747137, 35983214654363482, 36983105536126887, 31755700663962484,
    39607356968366506, 40470191398103005, 39607356968366506, 13496479326971103, 13496479326971103, 33186694919886862,
    34049529349630186, 33186694919886862, 13496479326971103, 13496479326971103, 7139551352398794, 29148744608984510,
    34380352463762947, 35380243345558368, 30152838491178177, 38240771592642654, 39103606022385978, 38240771592642654,
    8573647187496003, 8573647187496003, 39607356968366506, 40470191398103005, 39607356968366506, 17121826899172768,
    17121826899172768, 10701306462033270, 12480537783101981, 12480537783101981, 6870364722125690, 46888502845594812,
    27117214581447455, 22963409258418316, 48754102989381649, 28720076754092442, 44888502499008450, 28720076754092442,
    28720076754092442, 27117214581447455, 22963409258418316, 31583411547863479, 27442990756697836, 31583411547863479,
    27442990756697836, 23019854869527498, 13496479326971103, 13496479326971103, 10701306462033270, 3906890600547867,
    24994939294741471, 30226547127683909, 31226438009479329, 25999033178413158, 33186694919886862, 34049529349630186,
    33186694919886862, 9796039609425563, 9796039609425563, 33186694919886862
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
noncomputable def negativeCeiling : ℝ := 1493070031 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 16674229815050202178652209152, coefficient := (-16674229815050202178652209152) }, { argument := 626493649033046352831828721664, coefficient := (-626493649033046352831828721664) }, { argument := 626446265992960545547593187328, coefficient := (-626446265992960545547593187328) }, { argument := 16721612855136009462887743488, coefficient := (-16721612855136009462887743488) }, { argument := 1931222141381103124469765898240, coefficient := (-1931222141381103124469765898240) }, { argument := 7024271222097021565458500812800, coefficient := (-7024271222097021565458500812800) }, { argument := 1931222141381103124469765898240, coefficient := (-1931222141381103124469765898240) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 10979085969465854455487397888, coefficient := (-10979085969465854455487397888) }, { argument := 412512464344817203960784879616, coefficient := (-412512464344817203960784879616) }, { argument := 412481265154427782148476895232, coefficient := (-412481265154427782148476895232) }, { argument := 11010285159855276267795382272, coefficient := (-11010285159855276267795382272) }, { argument := 374471738179604302345304801280, coefficient := (-374471738179604302345304801280) }, { argument := 1362034432819072275014326681600, coefficient := (-1362034432819072275014326681600) }, { argument := 374471738179604302345304801280, coefficient := (-374471738179604302345304801280) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 117913788741932471184141582336, coefficient := (-117913788741932471184141582336) }, { argument := 1931222141381103124469765898240, coefficient := (-1931222141381103124469765898240) }, { argument := 7024271222097021565458500812800, coefficient := (-7024271222097021565458500812800) }, { argument := 1931222141381103124469765898240, coefficient := (-1931222141381103124469765898240) }, { argument := 2758691349108128440412312436736, coefficient := (-2758691349108128440412312436736) }, { argument := 2758691349108128440412312436736, coefficient := (-2758691349108128440412312436736) }, { argument := 32205783834533721214172528640, coefficient := (-32205783834533721214172528640) }, { argument := 221088353891123383470265466880, coefficient := (-221088353891123383470265466880) }, { argument := 221088353891123383470265466880, coefficient := (-221088353891123383470265466880) }, { argument := 72419492298194746081598767104, coefficient := (-72419492298194746081598767104) }, { argument := 146671451679447545567353241600, coefficient := (-146671451679447545567353241600) }, { argument := 10741741619371001236873543680, coefficient := (-10741741619371001236873543680) }, { argument := 603468630301741642520985600, coefficient := (-603468630301741642520985600) }, { argument := 534499366265944485877063352320, coefficient := (-534499366265944485877063352320) }, { argument := 16313768639157082402817310720, coefficient := (-16313768639157082402817310720) }, { argument := 146671416443785086479137505280, coefficient := (-146671416443785086479137505280) }, { argument := 16313768639157082402817310720, coefficient := (-16313768639157082402817310720) }, { argument := 16313768639157082402817310720, coefficient := (-16313768639157082402817310720) }, { argument := 10741741619371001236873543680, coefficient := (-10741741619371001236873543680) }, { argument := 603468630301741642520985600, coefficient := (-603468630301741642520985600) }, { argument := 237429104841091497866165223424, coefficient := (-237429104841091497866165223424) }, { argument := 13463038951985824737488011264, coefficient := (-13463038951985824737488011264) }, { argument := 237429104841091497866165223424, coefficient := (-237429104841091497866165223424) }, { argument := 13463038951985824737488011264, coefficient := (-13463038951985824737488011264) }, { argument := 80326065497866701409276133376, coefficient := (-80326065497866701409276133376) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 223544891156580309953268416512, coefficient := (-223544891156580309953268416512) }, { argument := 32205783834533721214172528640, coefficient := (-32205783834533721214172528640) }, { argument := 2321137573660088015435857920, coefficient := (-2321137573660088015435857920) }, { argument := 616802582554261486263336960, coefficient := (-616802582554261486263336960) }, { argument := 23174857547461640671954206720, coefficient := (-23174857547461640671954206720) }, { argument := 23173104783956616974633533440, coefficient := (-23173104783956616974633533440) }, { argument := 618555346059285183584010240, coefficient := (-618555346059285183584010240) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 163990767831058869232494182400, coefficient := (-163990767831058869232494182400) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 8597880429099242690510323712, coefficient := (-8597880429099242690510323712) }, { argument := 45086898242360384228866129920, coefficient := (-45086898242360384228866129920) }] }

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

end TermShard3


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
