import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 22, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1400271358783749094441815067590656
def positiveArguments : Array ℕ := #[
    187, 45, 35, 5, 47, 555,
    39, 35, 555, 5, 39, 39,
    39, 39, 39, 45, 47, 25,
    105, 455, 15, 15, 35, 455,
    455, 15, 5615, 225, 105, 455,
    35, 225, 35, 455, 455, 15,
    25, 475
  ]
def positiveCoefficients : Array ℕ := #[
    14815666390167431129992718712832, 1740853180245066011576893440, 1353996917968384675670917120, 1547425049106725343623905280, 1818224432700402278758088704, 21470522556355814142781685760,
    48279661532129830721065844736, 1353996917968384675670917120, 21470522556355814142781685760, 1547425049106725343623905280, 1508739422879057210033307648, 1508739422879057210033307648,
    1508739422879057210033307648, 48279661532129830721065844736, 1508739422879057210033307648, 1740853180245066011576893440, 1818224432700402278758088704, 1934281311383406679529881600,
    32495926031241232216102010880, 70407839734356003134887690240, 2321137573660088015435857920, 37138201178561408246973726720, 2707993835936769351341834240, 70407839734356003134887690240,
    70407839734356003134887690240, 37138201178561408246973726720, 868879165073426280444822814720, 69634127209802640463075737600, 32495926031241232216102010880, 70407839734356003134887690240,
    2707993835936769351341834240, 69634127209802640463075737600, 2707993835936769351341834240, 70407839734356003134887690240, 70407839734356003134887690240, 2321137573660088015435857920,
    61897001964269013744956211200, 73502689832569453822135500800
  ]
def positiveScales : Array ℕ := #[
    7, 5, 5, 2, 5, 9,
    5, 5, 9, 2, 5, 5,
    5, 5, 5, 5, 5, 4,
    6, 8, 3, 3, 5, 8,
    8, 3, 12, 7, 6, 8,
    5, 7, 5, 8, 8, 3,
    4, 8
  ]
def negativeArguments : Array ℕ := #[
    4745649951, 331637733, 225, 225, 39, 35,
    35, 39, 2800497343, 10018594341, 700124103, 455,
    455, 39, 455, 455, 39, 39,
    67147089, 4740783, 67147089, 4740783, 70727, 47,
    1, 5
  ]
def negativeCoefficients : Array ℕ := #[
    21885447527377318503675592704, 6117636385836220598376726528, 17408531802450660115768934400, 17408531802450660115768934400, 754369711439528605016653824, 676998458984192337835458560,
    676998458984192337835458560, 754369711439528605016653824, 6457507220678074431791169536, 23101305723342725087213125632, 6457505073938232853842100224, 17601959933589000783721922560,
    17601959933589000783721922560, 754369711439528605016653824, 17601959933589000783721922560, 17601959933589000783721922560, 24139830766064915360532922368, 754369711439528605016653824,
    619322583038798911254822912, 43726005354996494619377664, 619322583038798911254822912, 43726005354996494619377664, 1335995256935685588116307968, 909112216350201139379044352,
    158456325028528675187087900672, 1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    32, 28, 7, 7, 5, 5,
    5, 5, 31, 33, 29, 8,
    8, 5, 8, 8, 5, 5,
    26, 22, 26, 22, 16, 5,
    0, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7546894459887560, 5491853096329661, 5129283016944966, 2321928094887362, 5554588851677541, 9116343961237468,
    5285402218862248, 5129283016944966, 9116343961237468, 2321928094887362, 5285402218862248, 5285402218862248,
    5285402218862248, 5285402218862248, 5285402218862248, 5491853096329661, 5554588851677541, 4643856189773592,
    6714245517659862, 8829722735013603, 3906890595303263, 3906890595303263, 5129283016944966, 8829722735013603,
    8829722735013603, 3906890595303263, 12455070307287959, 7813781191164178, 6714245517659862, 8829722735013603,
    5129283016944966, 7813781191164178, 5129283016944966, 8829722735013603, 8829722735013603, 3906890595303263,
    4643856189773592, 8891783702985444
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32143958542259094, 28305032921888498, 7813781192070436, 7813781192070436, 5285402218862249, 5129283016944967,
    5129283016944967, 5285402218862249, 31383035913500766, 33221961054260367, 29383035433889775, 8829722736256263,
    8829722736256263, 5285402218862249, 8829722736256263, 8829722736256263, 5285402218862249, 5285402218862249,
    26000821520658055, 22176693927377151, 26000821520658055, 22176693927377151, 16109973447908839, 5554588851679165,
    0, 2321928094887363
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 1567020843 / 1000000000000
noncomputable def negativeCeiling : ℝ := 82101063 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 6457507220678074431791169536, coefficient := (-6457507220678074431791169536) }, { argument := 23101305723342725087213125632, coefficient := (-23101305723342725087213125632) }, { argument := 6457505073938232853842100224, coefficient := (-6457505073938232853842100224) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 24139830766064915360532922368, coefficient := (-24139830766064915360532922368) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 619322583038798911254822912, coefficient := (-619322583038798911254822912) }, { argument := 43726005354996494619377664, coefficient := (-43726005354996494619377664) }, { argument := 619322583038798911254822912, coefficient := (-619322583038798911254822912) }, { argument := 43726005354996494619377664, coefficient := (-43726005354996494619377664) }, { argument := 1335995256935685588116307968, coefficient := (-1335995256935685588116307968) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 14815666390167431129992718712832, coefficient := 14815666390167431129992718712832 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 868879165073426280444822814720, coefficient := 868879165073426280444822814720 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 2707993835936769351341834240, coefficient := 2707993835936769351341834240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 61897001964269013744956211200, coefficient := 61897001964269013744956211200 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-458676463600840806235660038963200)
def positiveArguments : Array ℕ := #[
    725, 7475, 225, 725, 225, 225,
    19275, 225, 7475, 19275, 25, 225,
    225, 475, 825, 14685, 825, 26125,
    44605, 825, 44605, 44605, 14685, 825,
    483, 541, 483, 541, 1, 1,
    5, 5, 75201325, 269027775, 18800325, 760265,
    28075575, 224604545, 6082175, 2191, 349787, 13961393,
    349787, 8763, 49293, 4145011, 2072505, 24647
  ]
def positiveCoefficients : Array ℕ := #[
    56094158030118793706366566400, 578350112103638597179434598400, 69634127209802640463075737600, 56094158030118793706366566400, 69634127209802640463075737600, 69634127209802640463075737600,
    2982661782153213099835077427200, 69634127209802640463075737600, 578350112103638597179434598400, 2982661782153213099835077427200, 61897001964269013744956211200, 69634127209802640463075737600,
    69634127209802640463075737600, 73502689832569453822135500800, 31915641637826210212243046400, 568098421153306541777926225920, 31915641637826210212243046400, 505330992598914995027181568000,
    862786178942568549404303687680, 31915641637826210212243046400, 862786178942568549404303687680, 862786178942568549404303687680, 568098421153306541777926225920, 31915641637826210212243046400,
    149481259743709668194069250048, 167431390313347682180106551296, 149481259743709668194069250048, 167431390313347682180106551296, 158456325028528675187087900672, 158456325028528675187087900672,
    792281625142643375935439503360, 792281625142643375935439503360, 1420512866589548489399389388800, 5081790990483985067520137625600, 1420512394352900202434868019200, 57443999265582253094249431040,
    2121330469876687030728209203200, 2121329950416373915067235696640, 57444518725895368755222937600, 331094558846956565222653952, 52858316958192786891618648064, 527446514858967076791830708224,
    52858316958192786891618648064, 331056779915093608060944384, 931118444160373686074867712, 78297044070103963907469082624, 78297025180638032428888227840, 931137333626305164655722496
  ]
def positiveScales : Array ℕ := #[
    9, 12, 7, 9, 7, 7,
    14, 7, 12, 14, 4, 7,
    7, 8, 9, 13, 9, 14,
    15, 9, 15, 15, 13, 9,
    8, 9, 8, 9, 0, 0,
    2, 2, 26, 28, 24, 19,
    24, 27, 22, 11, 18, 23,
    18, 13, 15, 21, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    25, 55, 1, 1, 1, 5,
    25, 55, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    7922816251426433759354395033600, 4357548938284538567644917268480, 633825300114114700748351602688, 158456325028528675187087900672, 158456325028528675187087900672, 1584563250285286751870879006720,
    7922816251426433759354395033600, 4357548938284538567644917268480, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 5, 0, 0, 0, 2,
    4, 5, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9501837184902278, 12867857863822738, 7813781191164178, 9501837184902278, 7813781191164178, 7813781191164178,
    14234443239689758, 7813781191164178, 12867857863822738, 14234443239689758, 4643856189773592, 7813781191164178,
    7813781191164178, 8891783702985444, 9688250309129776, 13842055645120155, 9688250309129776, 14673143416740609,
    15444917817741929, 9688250309129776, 15444917817741929, 15444917817741929, 13842055645120155, 9688250309129776,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 0, 0,
    2321928094887362, 2321928094887362, 26164254745716692, 28003179886476297, 24164254266105701, 19536142850292803,
    24742812234150653, 27742811880870992, 22536155896380102, 11097373768990222, 18416117146246269, 23734939558036408,
    18416117146246269, 13097209143550334, 15589095166470589, 21982944498554210, 20982944150498393, 14589124433920475
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4643856189792934, 5781359713964302, 0, 0, 0, 2321928094887363,
    4643856189792934, 5781359713964302, 0, 0
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 1262039631 / 200000000000
noncomputable def negativeCeiling : ℝ := 153652131 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56094158030118793706366566400, coefficient := 56094158030118793706366566400 }, { argument := 578350112103638597179434598400, coefficient := 578350112103638597179434598400 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 56094158030118793706366566400, coefficient := 56094158030118793706366566400 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 2982661782153213099835077427200, coefficient := 2982661782153213099835077427200 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 578350112103638597179434598400, coefficient := 578350112103638597179434598400 }, { argument := 2982661782153213099835077427200, coefficient := 2982661782153213099835077427200 }, { argument := 61897001964269013744956211200, coefficient := 61897001964269013744956211200 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 568098421153306541777926225920, coefficient := 568098421153306541777926225920 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 505330992598914995027181568000, coefficient := 505330992598914995027181568000 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 568098421153306541777926225920, coefficient := 568098421153306541777926225920 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 167431390313347682180106551296, coefficient := 167431390313347682180106551296 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1420512866589548489399389388800, coefficient := 1420512866589548489399389388800 }, { argument := 5081790990483985067520137625600, coefficient := 5081790990483985067520137625600 }, { argument := 1420512394352900202434868019200, coefficient := 1420512394352900202434868019200 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 57443999265582253094249431040, coefficient := 57443999265582253094249431040 }, { argument := 2121330469876687030728209203200, coefficient := 2121330469876687030728209203200 }, { argument := 2121329950416373915067235696640, coefficient := 2121329950416373915067235696640 }, { argument := 57444518725895368755222937600, coefficient := 57444518725895368755222937600 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 331094558846956565222653952, coefficient := 331094558846956565222653952 }, { argument := 52858316958192786891618648064, coefficient := 52858316958192786891618648064 }, { argument := 527446514858967076791830708224, coefficient := 527446514858967076791830708224 }, { argument := 52858316958192786891618648064, coefficient := 52858316958192786891618648064 }, { argument := 331056779915093608060944384, coefficient := 331056779915093608060944384 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 931118444160373686074867712, coefficient := 931118444160373686074867712 }, { argument := 78297044070103963907469082624, coefficient := 78297044070103963907469082624 }, { argument := 78297025180638032428888227840, coefficient := 78297025180638032428888227840 }, { argument := 931137333626305164655722496, coefficient := 931137333626305164655722496 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
