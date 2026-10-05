import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1399941657339957162248895278874624)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    750551, 17009705, 15, 141, 1665, 117,
    8504853, 1665, 15, 117, 117, 117,
    117, 117, 375275, 141, 1543103619, 26471742609,
    11739, 152087087451, 387, 903, 11739, 11739,
    387, 144867, 5805, 26471742609, 11739, 903,
    5805, 903, 11739, 11739, 1813616259, 8103512471247,
    10234990167, 219792371115441, 161066424207, 4848153237, 1758337766404695, 4848153237,
    4848153237, 415325127303, 4848153237, 161066424207, 415325127303, 64829302288809,
    4848153237, 4848153237, 10234990167, 17295229, 1277207407, 13312119205,
    1277207407, 17295229, 595177443, 22362345501, 44721308379, 1193737509,
    16283506011497, 72582615, 4077675, 59337963681299
  ]
def negativeCoefficients : Array ℕ := #[
    3544376886084295084784746496, 80326060775500218539630919680, 2321137573660088015435857920, 2727336649050603418137133056, 32205783834533721214172528640, 72419492298194746081598767104,
    80326065497866701409276133376, 32205783834533721214172528640, 2321137573660088015435857920, 2263109134318585815049961472, 2263109134318585815049961472, 2263109134318585815049961472,
    72419492298194746081598767104, 2263109134318585815049961472, 3544372163717812215139532800, 2727336649050603418137133056, 7116309384727002963379224576, 244158730546667687101776003072,
    227065283143298110110012801024, 1402755789562240283298295185408, 119770698800860541596490268672, 8733280120896081158077415424, 227065283143298110110012801024, 227065283143298110110012801024,
    119770698800860541596490268672, 2802135307361799754434553577472, 224570060251613515493419253760, 244158730546667687101776003072, 227065283143298110110012801024, 8733280120896081158077415424,
    224570060251613515493419253760, 8733280120896081158077415424, 227065283143298110110012801024, 227065283143298110110012801024, 8363828744422884313594331136, 145979902983600625525664514048,
    47200561051895696000934739968, 3959427362617511423477173714944, 371393888276758239586302296064, 44716320996532764632464490496, 3959424654785827321075319439360, 44716320996532764632464490496,
    44716320996532764632464490496, 1915349082684820085090562342912, 44716320996532764632464490496, 371393888276758239586302296064, 1915349082684820085090562342912, 145982610815284727927518789632,
    44716320996532764632464490496, 44716320996532764632464490496, 47200561051895696000934739968, 79760165764799893671510016, 11780159082987596645302009856, 122782628026674428829646192640,
    11780159082987596645302009856, 79760165764799893671510016, 10979085969465854455487397888, 412512464344817203960784879616, 412481265154427782148476895232, 11010285159855276267795382272,
    146668783211326241509709185024, 10711303384844736054134046720, 601758617126108767086182400, 534468862248044402935079108608
  ]
def negativeScales : Array ℕ := #[
    19, 24, 3, 7, 10, 6,
    23, 10, 3, 6, 6, 6,
    6, 6, 18, 7, 30, 34,
    13, 37, 8, 9, 13, 13,
    8, 17, 12, 34, 13, 9,
    12, 9, 13, 13, 30, 42,
    33, 47, 37, 32, 50, 32,
    32, 38, 32, 37, 38, 45,
    32, 32, 33, 24, 30, 33,
    30, 24, 29, 34, 35, 30,
    43, 26, 21, 45
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19517590580856519, 24019854784711506, 3906890600547867, 7139551352398794, 10701306462033270, 6870364722125690,
    23019854869527498, 10701306462033270, 3906890600547867, 6870364722125690, 6870364722125690, 6870364722125690,
    6870364722125690, 6870364722125690, 18517588658674013, 7139551352398794, 30523187795738781, 34623734118051353,
    13519021895622456, 37146106713843761, 8596189756149498, 9818582178420039, 13519021895622456, 13519021895622456,
    8596189756149498, 17144369467823856, 12503080351753230, 34623734118051353, 13519021895622456, 9818582178420039,
    12503080351753230, 9818582178420039, 13519021895622456, 13519021895622456, 30756222084198602, 42881684522180481,
    33252790665203961, 47643134640365363, 37228864825958480, 32174788153202688, 50643133653713425, 32174788153202688,
    32174788153202688, 38595450201680393, 32174788153202688, 37228864825958480, 38595450201680393, 45881711282982860,
    32174788153202688, 32174788153202688, 33252790665203961, 24043870780262774, 30250345678755404, 33632021206325742,
    30250345678755404, 24043870780262774, 29148744608984510, 34380352463762947, 35380243345558368, 30152838491178177,
    43888476597671643, 26113120699253788, 21959315375364084, 45754020652050333
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
noncomputable def negativeCeiling : ℝ := 2420779831 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3544376886084295084784746496, coefficient := (-3544376886084295084784746496) }, { argument := 80326060775500218539630919680, coefficient := (-80326060775500218539630919680) }, { argument := 2321137573660088015435857920, coefficient := (-2321137573660088015435857920) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 32205783834533721214172528640, coefficient := (-32205783834533721214172528640) }, { argument := 72419492298194746081598767104, coefficient := (-72419492298194746081598767104) }, { argument := 80326065497866701409276133376, coefficient := (-80326065497866701409276133376) }, { argument := 32205783834533721214172528640, coefficient := (-32205783834533721214172528640) }, { argument := 2321137573660088015435857920, coefficient := (-2321137573660088015435857920) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 72419492298194746081598767104, coefficient := (-72419492298194746081598767104) }, { argument := 2263109134318585815049961472, coefficient := (-2263109134318585815049961472) }, { argument := 3544372163717812215139532800, coefficient := (-3544372163717812215139532800) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 7116309384727002963379224576, coefficient := (-7116309384727002963379224576) }, { argument := 244158730546667687101776003072, coefficient := (-244158730546667687101776003072) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 1402755789562240283298295185408, coefficient := (-1402755789562240283298295185408) }, { argument := 119770698800860541596490268672, coefficient := (-119770698800860541596490268672) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 119770698800860541596490268672, coefficient := (-119770698800860541596490268672) }, { argument := 2802135307361799754434553577472, coefficient := (-2802135307361799754434553577472) }, { argument := 224570060251613515493419253760, coefficient := (-224570060251613515493419253760) }, { argument := 244158730546667687101776003072, coefficient := (-244158730546667687101776003072) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 224570060251613515493419253760, coefficient := (-224570060251613515493419253760) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 8363828744422884313594331136, coefficient := (-8363828744422884313594331136) }, { argument := 145979902983600625525664514048, coefficient := (-145979902983600625525664514048) }, { argument := 47200561051895696000934739968, coefficient := (-47200561051895696000934739968) }, { argument := 3959427362617511423477173714944, coefficient := (-3959427362617511423477173714944) }, { argument := 371393888276758239586302296064, coefficient := (-371393888276758239586302296064) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 3959424654785827321075319439360, coefficient := (-3959424654785827321075319439360) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 1915349082684820085090562342912, coefficient := (-1915349082684820085090562342912) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 371393888276758239586302296064, coefficient := (-371393888276758239586302296064) }, { argument := 1915349082684820085090562342912, coefficient := (-1915349082684820085090562342912) }, { argument := 145982610815284727927518789632, coefficient := (-145982610815284727927518789632) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 44716320996532764632464490496, coefficient := (-44716320996532764632464490496) }, { argument := 47200561051895696000934739968, coefficient := (-47200561051895696000934739968) }, { argument := 79760165764799893671510016, coefficient := (-79760165764799893671510016) }, { argument := 11780159082987596645302009856, coefficient := (-11780159082987596645302009856) }, { argument := 122782628026674428829646192640, coefficient := (-122782628026674428829646192640) }, { argument := 11780159082987596645302009856, coefficient := (-11780159082987596645302009856) }, { argument := 79760165764799893671510016, coefficient := (-79760165764799893671510016) }, { argument := 10979085969465854455487397888, coefficient := (-10979085969465854455487397888) }, { argument := 412512464344817203960784879616, coefficient := (-412512464344817203960784879616) }, { argument := 412481265154427782148476895232, coefficient := (-412481265154427782148476895232) }, { argument := 11010285159855276267795382272, coefficient := (-11010285159855276267795382272) }, { argument := 146668783211326241509709185024, coefficient := (-146668783211326241509709185024) }, { argument := 10711303384844736054134046720, coefficient := (-10711303384844736054134046720) }, { argument := 601758617126108767086182400, coefficient := (-601758617126108767086182400) }, { argument := 534468862248044402935079108608, coefficient := (-534468862248044402935079108608) }] }

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
def constantNumerator : ℤ := (-4682135342004732076063578579271680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    220466295, 4070875524897, 220466295, 220466295, 72582615, 4077675,
    33436935, 1256311545, 2512433055, 67063905, 20639621055, 37535375425,
    20639621055, 189420453, 2470747, 189420453, 2470747, 1543103619,
    26471742609, 11739, 152087087451, 387, 903, 11739,
    11739, 387, 144867, 5805, 26471742609, 11739,
    903, 5805, 903, 11739, 11739, 1813616259,
    29541320715733, 18613432745, 802178996033835, 292916652145, 8816889195, 6417418126550829,
    8816889195, 8816889195, 755313507705, 8816889195, 292916652145, 755313507705,
    236344407445715, 8816889195, 8816889195, 18613432745, 441090636151575, 2727115305,
    153208725, 1608978099140845, 8283485065, 110272622922495, 8283485065, 8283485065,
    2727115305, 153208725, 1807823619, 67924577533
  ]
def negativeCoefficients : Array ℕ := #[
    16267541282975807003563130880, 146668747975982412095129911296, 16267541282975807003563130880, 16267541282975807003563130880, 10711303384844736054134046720, 601758617126108767086182400,
    616802582554261486263336960, 23174857547461640671954206720, 23173104783956616974633533440, 618555346059285183584010240, 47591725922491516686025359360, 173101366043895473078743859200,
    47591725922491516686025359360, 6988381237634257315059204096, 91154475159771307053154304, 6988381237634257315059204096, 91154475159771307053154304, 7116309384727002963379224576,
    244158730546667687101776003072, 227065283143298110110012801024, 1402755789562240283298295185408, 119770698800860541596490268672, 8733280120896081158077415424, 227065283143298110110012801024,
    227065283143298110110012801024, 119770698800860541596490268672, 2802135307361799754434553577472, 224570060251613515493419253760, 244158730546667687101776003072, 227065283143298110110012801024,
    8733280120896081158077415424, 224570060251613515493419253760, 8733280120896081158077415424, 227065283143298110110012801024, 227065283143298110110012801024, 8363828744422884313594331136,
    532169123869629811965948854272, 171678615090110030834261032960, 14450772110489671578776386928640, 1350839629261655242616948654080, 162642898506420029211405189120, 14450740941707490013577679470592,
    162642898506420029211405189120, 162642898506420029211405189120, 6966537486024991251221855600640, 162642898506420029211405189120, 1350839629261655242616948654080, 6966537486024991251221855600640,
    532200292651811377164656312320, 162642898506420029211405189120, 162642898506420029211405189120, 171678615090110030834261032960, 3972991249217696403588277862400, 402451184726650930693448663040,
    22609617119474771387272396800, 14492386335475997024568203018240, 611213316129801319835930460160, 3972989948023325580893261660160, 611213316129801319835930460160, 611213316129801319835930460160,
    402451184726650930693448663040, 22609617119474771387272396800, 16674229815050202178652209152, 626493649033046352831828721664
  ]
def negativeScales : Array ℕ := #[
    27, 41, 27, 27, 26, 21,
    24, 30, 31, 25, 34, 35,
    34, 27, 21, 27, 21, 30,
    34, 13, 37, 8, 9, 13,
    13, 8, 17, 12, 34, 13,
    9, 12, 9, 13, 13, 30,
    44, 34, 49, 38, 33, 52,
    33, 33, 39, 33, 38, 39,
    47, 33, 33, 34, 48, 31,
    27, 50, 32, 46, 32, 32,
    31, 27, 30, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27715982871888462, 41888476251082110, 27715982871888462, 27715982871888462, 26113120699253788, 21959315375364084,
    24994939294741471, 30226547127683909, 31226438009479329, 25999033178413158, 34264697431888135, 35127531861631459,
    34264697431888135, 27497016875800667, 21236515858205170, 27497016875800667, 21236515858205170, 30523187795738781,
    34623734118051353, 13519021895622456, 37146106713843761, 8596189756149498, 9818582178420039, 13519021895622456,
    13519021895622456, 8596189756149498, 17144369467823856, 12503080351753230, 34623734118051353, 13519021895622456,
    9818582178420039, 12503080351753230, 9818582178420039, 13519021895622456, 13519021895622456, 30756222084198602,
    44747799560443283, 34115625094947285, 49510917520062628, 38091699255701804, 33037622582946012, 52510914408319142,
    33037622582946012, 33037622582946012, 39458284631418797, 33037622582946012, 38091699255701804, 39458284631418797,
    47747884055632660, 33037622582946012, 33037622582946012, 34115625094947285, 48648068462437128, 31344728554032223,
    27190923217953187, 50515066112034806, 32947590736569848, 46648067989939995, 32947590736569848, 32947590736569848,
    31344728554032223, 27190923217953187, 30751606781747137, 35983214654363482
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
noncomputable def negativeCeiling : ℝ := 10844299313 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16267541282975807003563130880, coefficient := (-16267541282975807003563130880) }, { argument := 146668747975982412095129911296, coefficient := (-146668747975982412095129911296) }, { argument := 16267541282975807003563130880, coefficient := (-16267541282975807003563130880) }, { argument := 16267541282975807003563130880, coefficient := (-16267541282975807003563130880) }, { argument := 10711303384844736054134046720, coefficient := (-10711303384844736054134046720) }, { argument := 601758617126108767086182400, coefficient := (-601758617126108767086182400) }, { argument := 616802582554261486263336960, coefficient := (-616802582554261486263336960) }, { argument := 23174857547461640671954206720, coefficient := (-23174857547461640671954206720) }, { argument := 23173104783956616974633533440, coefficient := (-23173104783956616974633533440) }, { argument := 618555346059285183584010240, coefficient := (-618555346059285183584010240) }, { argument := 47591725922491516686025359360, coefficient := (-47591725922491516686025359360) }, { argument := 173101366043895473078743859200, coefficient := (-173101366043895473078743859200) }, { argument := 47591725922491516686025359360, coefficient := (-47591725922491516686025359360) }, { argument := 6988381237634257315059204096, coefficient := (-6988381237634257315059204096) }, { argument := 91154475159771307053154304, coefficient := (-91154475159771307053154304) }, { argument := 6988381237634257315059204096, coefficient := (-6988381237634257315059204096) }, { argument := 91154475159771307053154304, coefficient := (-91154475159771307053154304) }, { argument := 7116309384727002963379224576, coefficient := (-7116309384727002963379224576) }, { argument := 244158730546667687101776003072, coefficient := (-244158730546667687101776003072) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 1402755789562240283298295185408, coefficient := (-1402755789562240283298295185408) }, { argument := 119770698800860541596490268672, coefficient := (-119770698800860541596490268672) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 119770698800860541596490268672, coefficient := (-119770698800860541596490268672) }, { argument := 2802135307361799754434553577472, coefficient := (-2802135307361799754434553577472) }, { argument := 224570060251613515493419253760, coefficient := (-224570060251613515493419253760) }, { argument := 244158730546667687101776003072, coefficient := (-244158730546667687101776003072) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 224570060251613515493419253760, coefficient := (-224570060251613515493419253760) }, { argument := 8733280120896081158077415424, coefficient := (-8733280120896081158077415424) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 227065283143298110110012801024, coefficient := (-227065283143298110110012801024) }, { argument := 8363828744422884313594331136, coefficient := (-8363828744422884313594331136) }, { argument := 532169123869629811965948854272, coefficient := (-532169123869629811965948854272) }, { argument := 171678615090110030834261032960, coefficient := (-171678615090110030834261032960) }, { argument := 14450772110489671578776386928640, coefficient := (-14450772110489671578776386928640) }, { argument := 1350839629261655242616948654080, coefficient := (-1350839629261655242616948654080) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 14450740941707490013577679470592, coefficient := (-14450740941707490013577679470592) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 6966537486024991251221855600640, coefficient := (-6966537486024991251221855600640) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 1350839629261655242616948654080, coefficient := (-1350839629261655242616948654080) }, { argument := 6966537486024991251221855600640, coefficient := (-6966537486024991251221855600640) }, { argument := 532200292651811377164656312320, coefficient := (-532200292651811377164656312320) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 162642898506420029211405189120, coefficient := (-162642898506420029211405189120) }, { argument := 171678615090110030834261032960, coefficient := (-171678615090110030834261032960) }, { argument := 3972991249217696403588277862400, coefficient := (-3972991249217696403588277862400) }, { argument := 402451184726650930693448663040, coefficient := (-402451184726650930693448663040) }, { argument := 22609617119474771387272396800, coefficient := (-22609617119474771387272396800) }, { argument := 14492386335475997024568203018240, coefficient := (-14492386335475997024568203018240) }, { argument := 611213316129801319835930460160, coefficient := (-611213316129801319835930460160) }, { argument := 3972989948023325580893261660160, coefficient := (-3972989948023325580893261660160) }, { argument := 611213316129801319835930460160, coefficient := (-611213316129801319835930460160) }, { argument := 611213316129801319835930460160, coefficient := (-611213316129801319835930460160) }, { argument := 402451184726650930693448663040, coefficient := (-402451184726650930693448663040) }, { argument := 22609617119474771387272396800, coefficient := (-22609617119474771387272396800) }, { argument := 16674229815050202178652209152, coefficient := (-16674229815050202178652209152) }, { argument := 626493649033046352831828721664, coefficient := (-626493649033046352831828721664) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
