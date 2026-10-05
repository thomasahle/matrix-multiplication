import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-92403565009022910604648109012156416)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3011882789, 2596839969372961121, 3011882789, 5866719587, 110936319165, 5868320099,
    68004932379, 110936319165, 33220518654915015, 5866719587, 5868320099, 6494903551,
    710653659877423461, 1575, 1305, 2596722567290377989, 8775, 355304176542791627,
    35145, 35145, 25155, 1305, 18135, 20475,
    8775, 231075, 20475, 8775, 20475, 20475,
    848835, 5265, 231075, 848835, 18135, 20475,
    5265, 20475, 18847819797, 41475, 34365, 138333062349,
    231075, 37695664905, 925485, 925485, 662415, 34365,
    6261287057748815, 6261286943198385, 834752427, 3675, 3045, 6126657779,
    20475, 1669505975, 82005, 82005, 58695, 3045,
    85320503765, 85320560171, 6385349, 9090675560638583
  ]
def negativeCoefficients : Array ℕ := #[
    27779715494346772948568768512, 730945469900554871857119154405376, 27779715494346772948568768512, 27055468693401999553643675648, 1023206944058057551790808760320, 27062849752214724809112682496,
    313617395836334262333122543616, 1023206944058057551790808760320, 18701489429416234068783849799680, 27055468693401999553643675648, 27062849752214724809112682496, 29952455897181093133344047104,
    200031222363340218940662183100416, 238007270736630118770278400, 12325376520289774007746560, 730912424152094002265014124150784, 331510127097449094001459200, 200018469635162162136040156954624,
    331935140080907362070691840, 331935140080907362070691840, 237582257753171850701045760, 12325376520289774007746560, 342560464667364063801507840, 386761814947023943001702400,
    331510127097449094001459200, 4364883340116413071019212800, 386761814947023943001702400, 331510127097449094001459200, 386761814947023943001702400, 386761814947023943001702400,
    16034039813946621179870576640, 397812152516938912801751040, 4364883340116413071019212800, 16034039813946621179870576640, 342560464667364063801507840, 386761814947023943001702400,
    397812152516938912801751040, 386761814947023943001702400, 86920227035663828544009535488, 3133762398032296563808665600, 162284124183815357768663040, 318974324760563706926620213248,
    4364883340116413071019212800, 86920285398856234751817154560, 4370479344398613600597442560, 4370479344398613600597442560, 3128166393750096034230435840, 162284124183815357768663040,
    14099165030068636251719854981120, 14099164772123999320154811924480, 7699232192888457552268886016, 277675149192735138565324800, 14379605940338069675704320, 28254222019103693448692105216,
    386761814947023943001702400, 7699237362588484209370726400, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320,
    196735687149115904521173729280, 196735817212496682228794785792, 60307916198050412391257079808, 5117595383429749651640361680896
  ]
def negativeScales : Array ℕ := #[
    31, 61, 31, 32, 36, 32,
    35, 36, 54, 32, 32, 32,
    59, 10, 10, 61, 13, 58,
    15, 15, 14, 10, 14, 14,
    13, 17, 14, 13, 14, 14,
    19, 12, 17, 19, 14, 14,
    12, 14, 34, 15, 15, 37,
    17, 35, 19, 19, 19, 15,
    52, 52, 29, 11, 11, 32,
    14, 30, 16, 16, 15, 11,
    36, 36, 22, 53
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31488018480895768, 61171462818444085, 31488018480895768, 32449906890803402, 36690940806985009, 32450300421767317,
    35984920355883321, 36690940806985009, 54882924118936867, 32449906890803402, 32450300421767317, 32596660955872863,
    59301924240561316, 10621136113284685, 10349834091457248, 61171397593311561, 13099183410079286, 58301832260499466,
    15101031834471655, 15101031834471655, 14618557569182239, 10349834091457248, 14146489124857643, 14321575831415734,
    13099183410079286, 17818001658463628, 14321575831415734, 13099183410079286, 14321575831415734, 14321575831415734,
    19695124618602028, 12362217815913081, 17818001658463628, 19695124618602028, 14146489124857643, 14321575831415734,
    12362217815913081, 14321575831415734, 34133678599690222, 15339954360730589, 15068652338913194, 37009355053368283,
    17818001658463628, 35133679568397539, 19819850082890743, 19819850082890743, 19337375816628813, 15068652338913194,
    52475380668483644, 52475380642089496, 29636773141970615, 11843528536141147, 11572226512796267, 32512453121928585,
    14321575831415734, 30636774110677352, 16323424255808103, 16323424255808103, 15840949991965165, 11572226512796267,
    36312173432802480, 36312174386578255, 22606334043888390, 53013308933545897
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
noncomputable def negativeCeiling : ℝ := 697269436091 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 27779715494346772948568768512, coefficient := (-27779715494346772948568768512) }, { argument := 730945469900554871857119154405376, coefficient := (-730945469900554871857119154405376) }, { argument := 27779715494346772948568768512, coefficient := (-27779715494346772948568768512) }, { argument := 27055468693401999553643675648, coefficient := (-27055468693401999553643675648) }, { argument := 1023206944058057551790808760320, coefficient := (-1023206944058057551790808760320) }, { argument := 27062849752214724809112682496, coefficient := (-27062849752214724809112682496) }, { argument := 313617395836334262333122543616, coefficient := (-313617395836334262333122543616) }, { argument := 1023206944058057551790808760320, coefficient := (-1023206944058057551790808760320) }, { argument := 18701489429416234068783849799680, coefficient := (-18701489429416234068783849799680) }, { argument := 27055468693401999553643675648, coefficient := (-27055468693401999553643675648) }, { argument := 27062849752214724809112682496, coefficient := (-27062849752214724809112682496) }, { argument := 29952455897181093133344047104, coefficient := (-29952455897181093133344047104) }, { argument := 200031222363340218940662183100416, coefficient := (-200031222363340218940662183100416) }, { argument := 238007270736630118770278400, coefficient := (-238007270736630118770278400) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 730912424152094002265014124150784, coefficient := (-730912424152094002265014124150784) }, { argument := 331510127097449094001459200, coefficient := (-331510127097449094001459200) }, { argument := 200018469635162162136040156954624, coefficient := (-200018469635162162136040156954624) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 237582257753171850701045760, coefficient := (-237582257753171850701045760) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 342560464667364063801507840, coefficient := (-342560464667364063801507840) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 331510127097449094001459200, coefficient := (-331510127097449094001459200) }, { argument := 4364883340116413071019212800, coefficient := (-4364883340116413071019212800) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 331510127097449094001459200, coefficient := (-331510127097449094001459200) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 16034039813946621179870576640, coefficient := (-16034039813946621179870576640) }, { argument := 397812152516938912801751040, coefficient := (-397812152516938912801751040) }, { argument := 4364883340116413071019212800, coefficient := (-4364883340116413071019212800) }, { argument := 16034039813946621179870576640, coefficient := (-16034039813946621179870576640) }, { argument := 342560464667364063801507840, coefficient := (-342560464667364063801507840) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 397812152516938912801751040, coefficient := (-397812152516938912801751040) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 86920227035663828544009535488, coefficient := (-86920227035663828544009535488) }, { argument := 3133762398032296563808665600, coefficient := (-3133762398032296563808665600) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 318974324760563706926620213248, coefficient := (-318974324760563706926620213248) }, { argument := 4364883340116413071019212800, coefficient := (-4364883340116413071019212800) }, { argument := 86920285398856234751817154560, coefficient := (-86920285398856234751817154560) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 3128166393750096034230435840, coefficient := (-3128166393750096034230435840) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 14099165030068636251719854981120, coefficient := (-14099165030068636251719854981120) }, { argument := 14099164772123999320154811924480, coefficient := (-14099164772123999320154811924480) }, { argument := 7699232192888457552268886016, coefficient := (-7699232192888457552268886016) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 28254222019103693448692105216, coefficient := (-28254222019103693448692105216) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 7699237362588484209370726400, coefficient := (-7699237362588484209370726400) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 196735687149115904521173729280, coefficient := (-196735687149115904521173729280) }, { argument := 196735817212496682228794785792, coefficient := (-196735817212496682228794785792) }, { argument := 60307916198050412391257079808, coefficient := (-60307916198050412391257079808) }, { argument := 5117595383429749651640361680896, coefficient := (-5117595383429749651640361680896) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-92143935944362104203336054342680576)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1770595795, 44413612935650403, 18528953535, 820630145, 11103404067443133, 820630145,
    1598148455, 30197577273, 1598234471, 18528953535, 30197577273, 9090727533116625,
    1598148455, 1598234471, 1770595795, 88831714225262879, 1575, 1305,
    1298361380728859565, 8775, 355304203500113879, 35145, 35145, 25155,
    1305, 127027407505573013, 127027403156634475, 834752427, 3675, 3045,
    6126657779, 20475, 1669505975, 82005, 82005, 58695,
    3045, 26969365795, 26969383645, 719323451, 3204447185, 3204449327,
    947, 72633, 82005, 35145, 925485, 82005,
    35145, 82005, 82005, 3399693, 21087, 925485,
    3399693, 72633, 82005, 21087, 82005, 1625649741,
    3675, 3045, 11933808197, 20475
  ]
def negativeCoefficients : Array ℕ := #[
    8165431872087825535656263680, 200021130667172595891406412709888, 85449715953450224244637040640, 7568977131993080015261532160, 200021145682723773663531208015872, 7568977131993080015261532160,
    7370158885294831508463288320, 278523489800549496341171011584, 7370555564079392558661238784, 85449715953450224244637040640, 278523489800549496341171011584, 5117624641333842585701056512000,
    7370158885294831508463288320, 7370555564079392558661238784, 8165431872087825535656263680, 200031237541788145317474564308992, 238007270736630118770278400, 12325376520289774007746560,
    730912478805341827897987726049280, 331510127097449094001459200, 200018484810785468262737665589248, 331935140080907362070691840, 331935140080907362070691840, 237582257753171850701045760,
    12325376520289774007746560, 143020146276984692034812732506112, 143020141380515197236315317862400, 7699232192888457552268886016, 277675149192735138565324800, 14379605940338069675704320,
    28254222019103693448692105216, 386761814947023943001702400, 7699237362588484209370726400, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720,
    14379605940338069675704320, 124374247162655335029334343680, 124374329481250763958208430080, 6793817910689051156522878369792, 7388952139926750647937925120, 7388957079042476383670370304,
    18317644018800861255147978752, 342999644750270940806381568, 387257663427725255749140480, 331935140080907362070691840, 4370479344398613600597442560, 387257663427725255749140480,
    331935140080907362070691840, 387257663427725255749140480, 387257663427725255749140480, 16054596275246552745485795328, 398322168097088834484830208, 4370479344398613600597442560,
    16054596275246552745485795328, 342999644750270940806381568, 387257663427725255749140480, 398322168097088834484830208, 387257663427725255749140480, 7496986181429804373444132864,
    277675149192735138565324800, 14379605940338069675704320, 27517488204349527409026924544, 386761814947023943001702400
  ]
def negativeScales : Array ℕ := #[
    30, 55, 34, 29, 53, 29,
    30, 34, 30, 34, 34, 53,
    30, 30, 30, 56, 10, 10,
    60, 13, 58, 15, 15, 14,
    10, 56, 56, 29, 11, 11,
    32, 14, 30, 16, 16, 15,
    11, 34, 34, 29, 31, 31,
    9, 16, 16, 15, 19, 16,
    15, 16, 16, 21, 14, 19,
    21, 16, 16, 14, 16, 30,
    11, 11, 33, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30721587754447084, 55301851453887732, 34109062353039780, 29612156910221487, 53301851562190592, 29612156910221487,
    30573754283121183, 34813713757672406, 30573831930173835, 34109062353039780, 34813713757672406, 53013317181582195,
    30573754283121183, 30573831930173835, 30721587754447084, 56301924350033580, 10621136113284685, 10349834091457248,
    60171397701187641, 13099183410079286, 58301832369958336, 15101031834471655, 15101031834471655, 14618557569182239,
    10349834091457248, 56817917421296116, 56817917371903686, 29636773141970615, 11843528536141147, 11572226512796267,
    32512453121928585, 14321575831415734, 30636774110677352, 16323424255808103, 16323424255808103, 15840949991965165,
    11572226512796267, 34650602544804468, 34650603499669264, 29422065397945694, 31577428345856933, 31577429310220384,
    9887220618935413, 16148337549250011, 16323424255808103, 15101031834471655, 19819850082890743, 16323424255808103,
    15101031834471655, 16323424255808103, 16323424255808103, 21696973042997282, 14364066240305450, 19819850082890743,
    21696973042997282, 16148337549250011, 16323424255808103, 14364066240305450, 16323424255808103, 30598369304912807,
    11843528536141147, 11572226512796267, 33474335443728138, 14321575831415734
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
noncomputable def negativeCeiling : ℝ := 126858505609 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8165431872087825535656263680, coefficient := (-8165431872087825535656263680) }, { argument := 200021130667172595891406412709888, coefficient := (-200021130667172595891406412709888) }, { argument := 85449715953450224244637040640, coefficient := (-85449715953450224244637040640) }, { argument := 7568977131993080015261532160, coefficient := (-7568977131993080015261532160) }, { argument := 200021145682723773663531208015872, coefficient := (-200021145682723773663531208015872) }, { argument := 7568977131993080015261532160, coefficient := (-7568977131993080015261532160) }, { argument := 7370158885294831508463288320, coefficient := (-7370158885294831508463288320) }, { argument := 278523489800549496341171011584, coefficient := (-278523489800549496341171011584) }, { argument := 7370555564079392558661238784, coefficient := (-7370555564079392558661238784) }, { argument := 85449715953450224244637040640, coefficient := (-85449715953450224244637040640) }, { argument := 278523489800549496341171011584, coefficient := (-278523489800549496341171011584) }, { argument := 5117624641333842585701056512000, coefficient := (-5117624641333842585701056512000) }, { argument := 7370158885294831508463288320, coefficient := (-7370158885294831508463288320) }, { argument := 7370555564079392558661238784, coefficient := (-7370555564079392558661238784) }, { argument := 8165431872087825535656263680, coefficient := (-8165431872087825535656263680) }, { argument := 200031237541788145317474564308992, coefficient := (-200031237541788145317474564308992) }, { argument := 238007270736630118770278400, coefficient := (-238007270736630118770278400) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 730912478805341827897987726049280, coefficient := (-730912478805341827897987726049280) }, { argument := 331510127097449094001459200, coefficient := (-331510127097449094001459200) }, { argument := 200018484810785468262737665589248, coefficient := (-200018484810785468262737665589248) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 237582257753171850701045760, coefficient := (-237582257753171850701045760) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 143020146276984692034812732506112, coefficient := (-143020146276984692034812732506112) }, { argument := 143020141380515197236315317862400, coefficient := (-143020141380515197236315317862400) }, { argument := 7699232192888457552268886016, coefficient := (-7699232192888457552268886016) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 28254222019103693448692105216, coefficient := (-28254222019103693448692105216) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 7699237362588484209370726400, coefficient := (-7699237362588484209370726400) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 124374247162655335029334343680, coefficient := (-124374247162655335029334343680) }, { argument := 124374329481250763958208430080, coefficient := (-124374329481250763958208430080) }, { argument := 6793817910689051156522878369792, coefficient := (-6793817910689051156522878369792) }, { argument := 7388952139926750647937925120, coefficient := (-7388952139926750647937925120) }, { argument := 7388957079042476383670370304, coefficient := (-7388957079042476383670370304) }, { argument := 18317644018800861255147978752, coefficient := (-18317644018800861255147978752) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 7496986181429804373444132864, coefficient := (-7496986181429804373444132864) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 27517488204349527409026924544, coefficient := (-27517488204349527409026924544) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
