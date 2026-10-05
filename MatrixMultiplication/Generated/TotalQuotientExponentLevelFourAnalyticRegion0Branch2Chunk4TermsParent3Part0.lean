import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4

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
def constantNumerator : ℤ := 322525181682620890430920720384
def positiveArguments : Array ℕ := #[
    21, 25165023, 25166625, 13508697, 96945403, 27032147,
    1984019, 36757355, 73533821, 981197, 128803, 3222265,
    43639563, 3214051, 63483
  ]
def positiveCoefficients : Array ℕ := #[
    3327582825599102178928845914112, 237676922311687455608999510016, 237692052773898569952264192000, 510344143520333821514556112896, 1831246887181961406835119357952, 510622819811220925017906741248,
    37477059307906202508927696896, 1388653610007527742750997872640, 1389014606590944229909713649664, 37068574607137978197942992896, 1216509940186117824919371776, 30433432469847914669020282880,
    412164019276556606181470109696, 30355853433267332137449684992, 1199159965728054748404252672
  ]
def positiveScales : Array ℕ := #[
    4, 24, 24, 23, 26, 24,
    20, 25, 26, 19, 16, 21,
    25, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    1080445741815, 27029469210897, 366063506369439, 26960568565779, 532518314019, 1487957557521,
    220690296789855, 220747288050897, 1471809956067, 1487957557521, 21378922102573, 5955562978447,
    1080445741815, 1080510010633, 1080510010633, 27031166703343, 366086868227169, 26962259296237,
    532549689309, 21378922102573, 197967887725055, 792078129628233, 10572681853511, 220690296789855,
    197967887725055, 220810321157285, 27029469210897, 27031166703343, 5955562978447, 220810321157285,
    110433690271603, 2945452241907, 220747288050897, 792078129628233, 110433690271603, 366063506369439,
    366086868227169, 1471809956067, 10572681853511, 2945452241907, 26960568565779, 26962259296237,
    532518314019, 532549689309, 3, 9, 9, 3
  ]
def negativeCoefficients : Array ℕ := #[
    304118440014504570535280640, 7608119216638626485011218432, 103037716929958916840944041984, 7588725409158688260986241024, 299781160072991647022972928, 3350582550797344483949150208,
    124237592298384393447942389760, 124269675526133409181140516864, 3314221384851763644245999616, 3350582550797344483949150208, 12035263201841327957948235776, 3352683901314428812566462464,
    304118440014504570535280640, 304136530078554341924405248, 304136530078554341924405248, 7608597018285330849498923008, 103044292708319386249791012864, 7589201307474977807738601472,
    299798822791035727179153408, 12035263201841327957948235776, 445784052694940943542533488640, 445900346180253695772979101696, 11903781513944736144098852864, 124237592298384393447942389760,
    445784052694940943542533488640, 124305160010438534385023057920, 7608119216638626485011218432, 7608597018285330849498923008, 3352683901314428812566462464, 124305160010438534385023057920,
    124337281589085010000737206272, 3316284404772489310626643968, 124269675526133409181140516864, 445900346180253695772979101696, 124337281589085010000737206272, 103037716929958916840944041984,
    103044292708319386249791012864, 3314221384851763644245999616, 11903781513944736144098852864, 3316284404772489310626643968, 7588725409158688260986241024, 7589201307474977807738601472,
    299781160072991647022972928, 299798822791035727179153408, 475368975085586025561263702016, 2852213850513516153367582212096, 2852213850513516153367582212096, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 44, 48, 44, 38, 40,
    47, 47, 40, 40, 44, 42,
    39, 39, 39, 44, 48, 44,
    38, 44, 47, 49, 43, 47,
    47, 47, 44, 44, 42, 47,
    46, 41, 47, 49, 46, 48,
    48, 40, 43, 41, 44, 44,
    38, 38, 1, 3, 3, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4392317422778759, 24584916580622348, 24585008419357939, 23687385188442768, 26530669153813886, 24688172765175940,
    20919994410730256, 25131529620564439, 26131904617103257, 19904183297022524, 16974806669671583, 21619643715902068,
    25379133319014909, 21615961390951236, 15954082685717236
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39974763778665209, 44619598414884274, 48379087283971844, 44615916155078328, 38954040197328202, 40436470514269555,
    47649016527699358, 47649389042469297, 40420728537529668, 40436470514269555, 44281254349621507, 42437375030923080,
    39974763778665209, 39974849592850806, 39974849592850806, 44619689015517945, 48379179352589095, 44616006625424388,
    38954125196565162, 44281254349621507, 47492259758844073, 49492636071440127, 43265406608932186, 47649016527699358,
    47492259758844073, 47649800936857562, 44619598414884274, 44619689015517945, 42437375030923080, 47649800936857562,
    46650173694156788, 41421626299721381, 47649389042469297, 49492636071440127, 46650173694156788, 48379087283971844,
    48379179352589095, 40420728537529668, 43265406608932186, 41421626299721381, 44615916155078328, 44616006625424388,
    38954040197328202, 38954125196565162, 1584962500724866, 3169925001442313, 3169925001442313, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 1108100047 / 500000000000
noncomputable def negativeCeiling : ℝ := 1078164489 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 304118440014504570535280640, coefficient := (-304118440014504570535280640) }, { argument := 7608119216638626485011218432, coefficient := (-7608119216638626485011218432) }, { argument := 103037716929958916840944041984, coefficient := (-103037716929958916840944041984) }, { argument := 7588725409158688260986241024, coefficient := (-7588725409158688260986241024) }, { argument := 299781160072991647022972928, coefficient := (-299781160072991647022972928) }, { argument := 3350582550797344483949150208, coefficient := (-3350582550797344483949150208) }, { argument := 124237592298384393447942389760, coefficient := (-124237592298384393447942389760) }, { argument := 124269675526133409181140516864, coefficient := (-124269675526133409181140516864) }, { argument := 3314221384851763644245999616, coefficient := (-3314221384851763644245999616) }, { argument := 3350582550797344483949150208, coefficient := (-3350582550797344483949150208) }, { argument := 12035263201841327957948235776, coefficient := (-12035263201841327957948235776) }, { argument := 3352683901314428812566462464, coefficient := (-3352683901314428812566462464) }, { argument := 304118440014504570535280640, coefficient := (-304118440014504570535280640) }, { argument := 304136530078554341924405248, coefficient := (-304136530078554341924405248) }, { argument := 304136530078554341924405248, coefficient := (-304136530078554341924405248) }, { argument := 7608597018285330849498923008, coefficient := (-7608597018285330849498923008) }, { argument := 103044292708319386249791012864, coefficient := (-103044292708319386249791012864) }, { argument := 7589201307474977807738601472, coefficient := (-7589201307474977807738601472) }, { argument := 299798822791035727179153408, coefficient := (-299798822791035727179153408) }, { argument := 12035263201841327957948235776, coefficient := (-12035263201841327957948235776) }, { argument := 445784052694940943542533488640, coefficient := (-445784052694940943542533488640) }, { argument := 445900346180253695772979101696, coefficient := (-445900346180253695772979101696) }, { argument := 11903781513944736144098852864, coefficient := (-11903781513944736144098852864) }, { argument := 124237592298384393447942389760, coefficient := (-124237592298384393447942389760) }, { argument := 445784052694940943542533488640, coefficient := (-445784052694940943542533488640) }, { argument := 124305160010438534385023057920, coefficient := (-124305160010438534385023057920) }, { argument := 7608119216638626485011218432, coefficient := (-7608119216638626485011218432) }, { argument := 7608597018285330849498923008, coefficient := (-7608597018285330849498923008) }, { argument := 3352683901314428812566462464, coefficient := (-3352683901314428812566462464) }, { argument := 124305160010438534385023057920, coefficient := (-124305160010438534385023057920) }, { argument := 124337281589085010000737206272, coefficient := (-124337281589085010000737206272) }, { argument := 3316284404772489310626643968, coefficient := (-3316284404772489310626643968) }, { argument := 124269675526133409181140516864, coefficient := (-124269675526133409181140516864) }, { argument := 445900346180253695772979101696, coefficient := (-445900346180253695772979101696) }, { argument := 124337281589085010000737206272, coefficient := (-124337281589085010000737206272) }, { argument := 103037716929958916840944041984, coefficient := (-103037716929958916840944041984) }, { argument := 103044292708319386249791012864, coefficient := (-103044292708319386249791012864) }, { argument := 3314221384851763644245999616, coefficient := (-3314221384851763644245999616) }, { argument := 11903781513944736144098852864, coefficient := (-11903781513944736144098852864) }, { argument := 3316284404772489310626643968, coefficient := (-3316284404772489310626643968) }, { argument := 7588725409158688260986241024, coefficient := (-7588725409158688260986241024) }, { argument := 7589201307474977807738601472, coefficient := (-7589201307474977807738601472) }, { argument := 299781160072991647022972928, coefficient := (-299781160072991647022972928) }, { argument := 299798822791035727179153408, coefficient := (-299798822791035727179153408) }, { argument := 3327582825599102178928845914112, coefficient := 3327582825599102178928845914112 }, { argument := 237676922311687455608999510016, coefficient := 237676922311687455608999510016 }, { argument := 237692052773898569952264192000, coefficient := 237692052773898569952264192000 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 510344143520333821514556112896, coefficient := 510344143520333821514556112896 }, { argument := 1831246887181961406835119357952, coefficient := 1831246887181961406835119357952 }, { argument := 510622819811220925017906741248, coefficient := 510622819811220925017906741248 }, { argument := 2852213850513516153367582212096, coefficient := (-2852213850513516153367582212096) }, { argument := 37477059307906202508927696896, coefficient := 37477059307906202508927696896 }, { argument := 1388653610007527742750997872640, coefficient := 1388653610007527742750997872640 }, { argument := 1389014606590944229909713649664, coefficient := 1389014606590944229909713649664 }, { argument := 37068574607137978197942992896, coefficient := 37068574607137978197942992896 }, { argument := 2852213850513516153367582212096, coefficient := (-2852213850513516153367582212096) }, { argument := 1216509940186117824919371776, coefficient := 1216509940186117824919371776 }, { argument := 30433432469847914669020282880, coefficient := 30433432469847914669020282880 }, { argument := 412164019276556606181470109696, coefficient := 412164019276556606181470109696 }, { argument := 30355853433267332137449684992, coefficient := 30355853433267332137449684992 }, { argument := 1199159965728054748404252672, coefficient := 1199159965728054748404252672 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4
