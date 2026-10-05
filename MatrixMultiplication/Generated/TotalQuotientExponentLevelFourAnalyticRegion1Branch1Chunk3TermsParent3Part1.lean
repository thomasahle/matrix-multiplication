import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3

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
def constantNumerator : ℤ := 3000299242497469756423137442922496
def positiveArguments : Array ℕ := #[
    441, 5, 6357, 6955, 6357, 6955,
    273, 45591, 1183, 49049, 73437, 2275,
    73437, 76531, 45591, 2275, 3131, 3535,
    1515, 39895
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 792281625142643375935439503360, 491849051858572650470858293248, 538117060826863738245213061120, 491849051858572650470858293248, 538117060826863738245213061120,
    42244703840613601880932614144, 881858192672808939264468320256, 45765095827331402037676998656, 948745640420447142242611625984, 1420478166640632363246359150592, 44004899833972501959304806400,
    1420478166640632363246359150592, 1480324830414834965911013687296, 881858192672808939264468320256, 44004899833972501959304806400, 60562347859414463136080592896, 68376844357403426121381314560,
    58608723734917222389755412480, 771681529176410094798446264320
  ]
def positiveScales : Array ℕ := #[
    8, 2, 12, 12, 12, 12,
    8, 15, 10, 15, 16, 11,
    16, 16, 15, 11, 11, 11,
    10, 15
  ]
def negativeArguments : Array ℕ := #[
    14973670635, 58109215421, 208286371807, 14531525465, 620765158605, 620765602611,
    459, 3850369695, 3850372449, 15, 34616785881, 124080228627,
    8656711365, 168988447725, 168988568595, 9, 620765158605, 620765602611,
    7353, 471, 31850350127, 1453643685, 31850359613, 1453643685,
    1778309, 459, 1727384525, 6191628175, 431971625, 14973659925,
    14973670635, 15, 3850369695, 3850372449, 471, 15,
    14973659925, 14973670635, 459, 15, 12583, 5,
    13, 91
  ]
def negativeCoefficients : Array ℕ := #[
    17263466877991561784469749760, 133990728149405429679932833792, 480275674345655185202179211264, 134029665626724093160817950720, 715693500666384601225604628480, 715694012570450175693303054336,
    17756702438499673318084313088, 17756696088208025943571169280, 17756708788791320692597456896, 18569100589280704123486863360, 79820873725151153709448691712, 286109527761204813063367163904,
    79844069535063936591640657920, 194830415412282506880850329600, 194830554765904768710444318720, 11141460353568422474092118016, 715693500666384601225604628480, 715694012570450175693303054336,
    284455409652043786291664388096, 18220929953231690921171484672, 36720953590675719667111165952, 3351874128944883028847493120, 36720964527289112367661580288, 3351874128944883028847493120,
    67182614542283487282580160512, 17756702438499673318084313088, 3983077531195167350770892800, 14276922542974292069030297600, 3984235006739717394792448000, 17263454530202247445138636800,
    17263466877991561784469749760, 580284393415022003858964480, 17756696088208025943571169280, 17756708788791320692597456896, 18220929953231690921171484672, 580284393415022003858964480,
    17263454530202247445138636800, 17263466877991561784469749760, 17756702438499673318084313088, 18569100589280704123486863360, 950744599263179931582988288, 792281625142643375935439503360,
    2059932225370872777432142708736, 7209762788798054721012499480576
  ]
def negativeScales : Array ℕ := #[
    33, 35, 37, 33, 39, 39,
    8, 31, 31, 3, 35, 36,
    33, 37, 37, 3, 39, 39,
    12, 8, 34, 30, 34, 30,
    20, 8, 30, 32, 28, 33,
    33, 3, 31, 31, 8, 3,
    33, 33, 8, 3, 13, 2,
    3, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2321928094887362, 12634130373092445, 12763834799410789, 12634130373092445, 12763834799410789,
    8092757140919852, 15476461433393896, 10208234358339788, 15581936102950989, 16164219503476476, 11151650829973420,
    16164219503476476, 16223756630453840, 15476461433393896, 11151650829973420, 11612407793138175, 11787494499665800,
    10565102078360182, 15283920325816259
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33801708875533234, 35758047924955517, 37599777490587968, 33758467108774797, 39175256630090196, 39175257661986101,
    8842350344909532, 31842349828961473, 31842350860857408, 3906890600547867, 35010752727627726, 36852482295338445,
    33011171911444570, 37298133669087917, 37298134700983822, 3169925001442313, 39175256630090196, 39175257661986101,
    12844117271135484, 8879583252627603, 34890590184498335, 30437026535293032, 34890590614176626, 30437026535293032,
    20762074599090391, 8842350344909532, 30685942124259061, 32527671690102595, 28686361308076430, 33801707843637314,
    33801708875533234, 3906890600547867, 31842349828961473, 31842350860857408, 8879583252627603, 3906890600547867,
    33801707843637314, 33801708875533234, 8842350344909532, 3906890600547867, 13619188305682172, 2321928094887363,
    3700439718214233, 6507794640199048
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 44
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
noncomputable def positiveFloor : ℝ := 278457827 / 50000000000
noncomputable def negativeCeiling : ℝ := 2902153681 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 133990728149405429679932833792, coefficient := (-133990728149405429679932833792) }, { argument := 480275674345655185202179211264, coefficient := (-480275674345655185202179211264) }, { argument := 134029665626724093160817950720, coefficient := (-134029665626724093160817950720) }, { argument := 715693500666384601225604628480, coefficient := (-715693500666384601225604628480) }, { argument := 715694012570450175693303054336, coefficient := (-715694012570450175693303054336) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 17756696088208025943571169280, coefficient := (-17756696088208025943571169280) }, { argument := 17756708788791320692597456896, coefficient := (-17756708788791320692597456896) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 79820873725151153709448691712, coefficient := (-79820873725151153709448691712) }, { argument := 286109527761204813063367163904, coefficient := (-286109527761204813063367163904) }, { argument := 79844069535063936591640657920, coefficient := (-79844069535063936591640657920) }, { argument := 194830415412282506880850329600, coefficient := (-194830415412282506880850329600) }, { argument := 194830554765904768710444318720, coefficient := (-194830554765904768710444318720) }, { argument := 11141460353568422474092118016, coefficient := (-11141460353568422474092118016) }, { argument := 715693500666384601225604628480, coefficient := (-715693500666384601225604628480) }, { argument := 715694012570450175693303054336, coefficient := (-715694012570450175693303054336) }, { argument := 284455409652043786291664388096, coefficient := (-284455409652043786291664388096) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 36720953590675719667111165952, coefficient := (-36720953590675719667111165952) }, { argument := 3351874128944883028847493120, coefficient := (-3351874128944883028847493120) }, { argument := 36720964527289112367661580288, coefficient := (-36720964527289112367661580288) }, { argument := 3351874128944883028847493120, coefficient := (-3351874128944883028847493120) }, { argument := 67182614542283487282580160512, coefficient := (-67182614542283487282580160512) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 3983077531195167350770892800, coefficient := (-3983077531195167350770892800) }, { argument := 14276922542974292069030297600, coefficient := (-14276922542974292069030297600) }, { argument := 3984235006739717394792448000, coefficient := (-3984235006739717394792448000) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }, { argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17756696088208025943571169280, coefficient := (-17756696088208025943571169280) }, { argument := 17756708788791320692597456896, coefficient := (-17756708788791320692597456896) }, { argument := 18220929953231690921171484672, coefficient := (-18220929953231690921171484672) }, { argument := 580284393415022003858964480, coefficient := (-580284393415022003858964480) }, { argument := 17263454530202247445138636800, coefficient := (-17263454530202247445138636800) }, { argument := 17263466877991561784469749760, coefficient := (-17263466877991561784469749760) }, { argument := 17756702438499673318084313088, coefficient := (-17756702438499673318084313088) }, { argument := 18569100589280704123486863360, coefficient := (-18569100589280704123486863360) }, { argument := 950744599263179931582988288, coefficient := (-950744599263179931582988288) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 491849051858572650470858293248, coefficient := 491849051858572650470858293248 }, { argument := 538117060826863738245213061120, coefficient := 538117060826863738245213061120 }, { argument := 491849051858572650470858293248, coefficient := 491849051858572650470858293248 }, { argument := 538117060826863738245213061120, coefficient := 538117060826863738245213061120 }, { argument := 2059932225370872777432142708736, coefficient := (-2059932225370872777432142708736) }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 881858192672808939264468320256, coefficient := 881858192672808939264468320256 }, { argument := 45765095827331402037676998656, coefficient := 45765095827331402037676998656 }, { argument := 948745640420447142242611625984, coefficient := 948745640420447142242611625984 }, { argument := 1420478166640632363246359150592, coefficient := 1420478166640632363246359150592 }, { argument := 44004899833972501959304806400, coefficient := 44004899833972501959304806400 }, { argument := 1420478166640632363246359150592, coefficient := 1420478166640632363246359150592 }, { argument := 1480324830414834965911013687296, coefficient := 1480324830414834965911013687296 }, { argument := 881858192672808939264468320256, coefficient := 881858192672808939264468320256 }, { argument := 44004899833972501959304806400, coefficient := 44004899833972501959304806400 }, { argument := 7209762788798054721012499480576, coefficient := (-7209762788798054721012499480576) }, { argument := 60562347859414463136080592896, coefficient := 60562347859414463136080592896 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 58608723734917222389755412480, coefficient := 58608723734917222389755412480 }, { argument := 771681529176410094798446264320, coefficient := 771681529176410094798446264320 }] }

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
def constantNumerator : ℤ := (-1323459124882711198480997422202880)
def positiveArguments : Array ℕ := #[
    3535, 1515, 3535, 3535, 146551, 909,
    39895, 146551, 3131, 3535, 909, 3535,
    9, 261, 231, 15, 9, 15,
    459, 15, 9, 7353, 471, 261,
    459, 15, 471, 15, 459, 15,
    9, 5, 1484783313, 1484783919, 969112729, 3514289831,
    15143635, 5247845, 417323317, 26082705, 10495729, 3367,
    3022085, 31677625, 1511045, 3367
  ]
def positiveCoefficients : Array ℕ := #[
    68376844357403426121381314560, 58608723734917222389755412480, 68376844357403426121381314560, 68376844357403426121381314560, 2834708604645496322917836783616, 70330468481900666867706494976,
    771681529176410094798446264320, 2834708604645496322917836783616, 60562347859414463136080592896, 68376844357403426121381314560, 70330468481900666867706494976, 68376844357403426121381314560,
    1392682544196052809261514752, 20193896890842765734291963904, 35745518634365355437712211968, 1160568786830044007717928960, 22282920707136844948184236032, 1160568786830044007717928960,
    35513404876999346636168626176, 37138201178561408246973726720, 22282920707136844948184236032, 568910819304087572583328776192, 36441859906463381842342969344, 20193896890842765734291963904,
    35513404876999346636168626176, 1160568786830044007717928960, 36441859906463381842342969344, 1160568786830044007717928960, 35513404876999346636168626176, 37138201178561408246973726720,
    1392682544196052809261514752, 1584563250285286751870879006720, 7011690951635349567526139854848, 7011693813389438186531139354624, 4576505469551933624306718736384, 16595764509004029873069674725376,
    4576882838579946220525390397440, 99128989341180213145873940480, 3941507289441568038385577099264, 3941506939986448306031831285760, 99129357685765876978200608768, 508806654330307053904461824,
    114171143299064894045059809280, 1196746836455308359700054016000, 114171332193724208830868357120, 508806654330307053904461824
  ]
def positiveScales : Array ℕ := #[
    11, 10, 11, 11, 17, 9,
    15, 17, 11, 11, 9, 11,
    3, 8, 7, 3, 3, 3,
    8, 3, 3, 12, 8, 8,
    8, 3, 8, 3, 8, 3,
    3, 2, 30, 30, 29, 31,
    23, 22, 28, 24, 23, 11,
    21, 24, 20, 11
  ]
def negativeArguments : Array ℕ := #[
    101, 3, 5, 177, 325, 51,
    9
  ]
def negativeCoefficients : Array ℕ := #[
    8002044413940698096947938983936, 950737950171172051122527404032, 1584563250285286751870879006720, 14023384765024787754057279209472, 25749152817135909717901783859200, 8081272576454962434541482934272,
    1426106925256758076683791106048
  ]
def negativeScales : Array ℕ := #[
    6, 1, 2, 7, 8, 5,
    3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11787494499665800, 10565102078360182, 11787494499665800, 11787494499665800, 17161043286818539, 9828136484123869,
    15283920325816259, 17161043286818539, 11612407793138175, 11787494499665800, 9828136484123869, 11787494499665800,
    3169925001442312, 8027905996569884, 7851749041305231, 3906890595303263, 3169925001442312, 3906890595303263,
    8842350343321225, 3906890595303263, 3169925001442312, 12844117269492213, 8879583249426338, 8027905996569884,
    8842350343321225, 3906890595303263, 8879583249426338, 3906890595303263, 8842350343321225, 3906890595303263,
    3169925001442312, 2321928094887362, 30467605255671982, 30467605844493940, 29852089251366592, 31710586032379604,
    23852208208064620, 22323293678564910, 28636590289285873, 24636590161376128, 23323299039337004, 11717248005820939,
    21527112808037963, 24916960838621630, 20527115194956014, 11717248005820939
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6658211482778016, 1584962500724866, 2321928094887363, 7467605550083086, 8344295907915818, 5672425342008812,
    3169925001442313
  ]

abbrev PositiveTerm := Fin 46
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
noncomputable def positiveFloor : ℝ := 18993313923 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5156751499 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 58608723734917222389755412480, coefficient := 58608723734917222389755412480 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 2834708604645496322917836783616, coefficient := 2834708604645496322917836783616 }, { argument := 70330468481900666867706494976, coefficient := 70330468481900666867706494976 }, { argument := 771681529176410094798446264320, coefficient := 771681529176410094798446264320 }, { argument := 2834708604645496322917836783616, coefficient := 2834708604645496322917836783616 }, { argument := 60562347859414463136080592896, coefficient := 60562347859414463136080592896 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 70330468481900666867706494976, coefficient := 70330468481900666867706494976 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 8002044413940698096947938983936, coefficient := (-8002044413940698096947938983936) }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 35745518634365355437712211968, coefficient := 35745518634365355437712211968 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 568910819304087572583328776192, coefficient := 568910819304087572583328776192 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 7011690951635349567526139854848, coefficient := 7011690951635349567526139854848 }, { argument := 7011693813389438186531139354624, coefficient := 7011693813389438186531139354624 }, { argument := 14023384765024787754057279209472, coefficient := (-14023384765024787754057279209472) }, { argument := 4576505469551933624306718736384, coefficient := 4576505469551933624306718736384 }, { argument := 16595764509004029873069674725376, coefficient := 16595764509004029873069674725376 }, { argument := 4576882838579946220525390397440, coefficient := 4576882838579946220525390397440 }, { argument := 25749152817135909717901783859200, coefficient := (-25749152817135909717901783859200) }, { argument := 99128989341180213145873940480, coefficient := 99128989341180213145873940480 }, { argument := 3941507289441568038385577099264, coefficient := 3941507289441568038385577099264 }, { argument := 3941506939986448306031831285760, coefficient := 3941506939986448306031831285760 }, { argument := 99129357685765876978200608768, coefficient := 99129357685765876978200608768 }, { argument := 8081272576454962434541482934272, coefficient := (-8081272576454962434541482934272) }, { argument := 508806654330307053904461824, coefficient := 508806654330307053904461824 }, { argument := 114171143299064894045059809280, coefficient := 114171143299064894045059809280 }, { argument := 1196746836455308359700054016000, coefficient := 1196746836455308359700054016000 }, { argument := 114171332193724208830868357120, coefficient := 114171332193724208830868357120 }, { argument := 508806654330307053904461824, coefficient := 508806654330307053904461824 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk3
