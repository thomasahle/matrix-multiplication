import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-121067914374387538817068721766400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    141453, 4216691, 5, 47, 555, 39,
    2108345, 555, 5, 39, 39, 39,
    39, 39, 70727, 47, 14165453, 389148081,
    455, 6806267379, 15, 35, 455, 455,
    15, 5615, 225, 389148081, 455, 35,
    225, 35, 455, 455, 67147089, 79504509,
    2914803357, 11064536787, 45869800197, 1380696327, 11064535167, 1380696327,
    1380696327, 118279652013, 1380696327, 45869800197, 118279652013, 1272072549,
    1380696327, 1380696327, 2914803357, 1185331, 189234767, 7553113613,
    189234767, 4740783, 99650007, 3679942185, 29439530271, 797207265,
    153200257, 25835187, 1451415, 619217389
  ]
def negativeCoefficients : Array ℕ := #[
    1335985812202719848825880576, 39825520494036174291569999872, 773712524553362671811952640, 909112216350201139379044352, 10735261278177907071390842880, 24139830766064915360532922368,
    39825511049303208552279572480, 10735261278177907071390842880, 773712524553362671811952640, 754369711439528605016653824, 754369711439528605016653824, 754369711439528605016653824,
    24139830766064915360532922368, 754369711439528605016653824, 1335995256935685588116307968, 909112216350201139379044352, 522612972358322378135044096, 14357030113964389125473697792,
    17601959933589000783721922560, 62776736218825446342348767232, 9284550294640352061743431680, 676998458984192337835458560, 17601959933589000783721922560, 17601959933589000783721922560,
    9284550294640352061743431680, 217219791268356570111205703680, 17408531802450660115768934400, 14357030113964389125473697792, 17601959933589000783721922560, 676998458984192337835458560,
    17408531802450660115768934400, 676998458984192337835458560, 17601959933589000783721922560, 17601959933589000783721922560, 619322583038798911254822912, 5866397320915750839360946176,
    6721078943971057061660196864, 12756542400245848338031706112, 52884279059140685827273654272, 6367337946919948795257028608, 12756540532513010874939604992, 6367337946919948795257028608,
    6367337946919948795257028608, 272734308726404473396842725376, 6367337946919948795257028608, 52884279059140685827273654272, 272734308726404473396842725376, 5866399188648588302453047296,
    6367337946919948795257028608, 6367337946919948795257028608, 6721078943971057061660196864, 43730995199268433053089792, 6981530633394115651456466944, 69665176889331344859467874304,
    6981530633394115651456466944, 43726005354996494619377664, 3676436352144730669002522624, 135765903385485056858306641920, 135765870139840550015267241984, 3676469597789237512041922560,
    5652091865811060501851930624, 3812600661483424397484097536, 214191048397945190869893120, 22845089401747304192040501248
  ]
def negativeScales : Array ℕ := #[
    17, 22, 2, 5, 9, 5,
    21, 9, 2, 5, 5, 5,
    5, 5, 16, 5, 23, 28,
    8, 32, 3, 5, 8, 8,
    3, 12, 7, 28, 8, 5,
    7, 5, 8, 8, 26, 26,
    31, 33, 35, 30, 33, 30,
    30, 36, 30, 35, 36, 30,
    30, 30, 31, 20, 27, 32,
    27, 22, 26, 31, 34, 29,
    27, 24, 20, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17109963248832529, 22007679873819777, 2321928094887363, 5554588851679165, 9116343961237469, 5285402218862249,
    21007679531680594, 9116343961237469, 2321928094887363, 5285402218862249, 5285402218862249, 5285402218862249,
    5285402218862249, 5285402218862249, 16109973447908839, 5554588851679165, 23755873403168870, 28535744001900451,
    8829722736256263, 32664216681602394, 3906890600547867, 5129283016944967, 8829722736256263, 8829722736256263,
    3906890600547867, 12455070307288020, 7813781192070436, 28535744001900451, 8829722736256263, 5129283016944967,
    7813781192070436, 5129283016944967, 8829722736256263, 8829722736256263, 26000821520658055, 26244533347595589,
    31440751411357083, 33365224003348625, 35416825572111582, 30362748899355778, 33365223792118260, 30362748899355778,
    30362748899355778, 36783410948287383, 30362748899355778, 35416825572111582, 36783410948287383, 30244533806918121,
    30362748899355778, 30362748899355778, 31440751411357083, 20176858552817038, 27495601930073321, 32814424342737678,
    27495601930073321, 22176693927377151, 26570366570621658, 31777035954890454, 34777035601610790, 29570379616708957,
    27190843476546590, 24622833990523865, 20469028654434414, 29205870745232083
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
noncomputable def negativeCeiling : ℝ := 292127911 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1335985812202719848825880576, coefficient := (-1335985812202719848825880576) }, { argument := 39825520494036174291569999872, coefficient := (-39825520494036174291569999872) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 10735261278177907071390842880, coefficient := (-10735261278177907071390842880) }, { argument := 24139830766064915360532922368, coefficient := (-24139830766064915360532922368) }, { argument := 39825511049303208552279572480, coefficient := (-39825511049303208552279572480) }, { argument := 10735261278177907071390842880, coefficient := (-10735261278177907071390842880) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 24139830766064915360532922368, coefficient := (-24139830766064915360532922368) }, { argument := 754369711439528605016653824, coefficient := (-754369711439528605016653824) }, { argument := 1335995256935685588116307968, coefficient := (-1335995256935685588116307968) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 522612972358322378135044096, coefficient := (-522612972358322378135044096) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 62776736218825446342348767232, coefficient := (-62776736218825446342348767232) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 619322583038798911254822912, coefficient := (-619322583038798911254822912) }, { argument := 5866397320915750839360946176, coefficient := (-5866397320915750839360946176) }, { argument := 6721078943971057061660196864, coefficient := (-6721078943971057061660196864) }, { argument := 12756542400245848338031706112, coefficient := (-12756542400245848338031706112) }, { argument := 52884279059140685827273654272, coefficient := (-52884279059140685827273654272) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 12756540532513010874939604992, coefficient := (-12756540532513010874939604992) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 272734308726404473396842725376, coefficient := (-272734308726404473396842725376) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 52884279059140685827273654272, coefficient := (-52884279059140685827273654272) }, { argument := 272734308726404473396842725376, coefficient := (-272734308726404473396842725376) }, { argument := 5866399188648588302453047296, coefficient := (-5866399188648588302453047296) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 6367337946919948795257028608, coefficient := (-6367337946919948795257028608) }, { argument := 6721078943971057061660196864, coefficient := (-6721078943971057061660196864) }, { argument := 43730995199268433053089792, coefficient := (-43730995199268433053089792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 69665176889331344859467874304, coefficient := (-69665176889331344859467874304) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 43726005354996494619377664, coefficient := (-43726005354996494619377664) }, { argument := 3676436352144730669002522624, coefficient := (-3676436352144730669002522624) }, { argument := 135765903385485056858306641920, coefficient := (-135765903385485056858306641920) }, { argument := 135765870139840550015267241984, coefficient := (-135765870139840550015267241984) }, { argument := 3676469597789237512041922560, coefficient := (-3676469597789237512041922560) }, { argument := 5652091865811060501851930624, coefficient := (-5652091865811060501851930624) }, { argument := 3812600661483424397484097536, coefficient := (-3812600661483424397484097536) }, { argument := 214191048397945190869893120, coefficient := (-214191048397945190869893120) }, { argument := 22845089401747304192040501248, coefficient := (-22845089401747304192040501248) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-301970934367169181822452435517440)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    78473171, 9575013, 78473171, 78473171, 25835187, 1451415,
    5598315, 206738325, 1653906195, 44786925, 2800497343, 10018594341,
    700124103, 14165453, 1185331, 14165453, 1185331, 14165453,
    389148081, 455, 6806267379, 15, 35, 455,
    455, 15, 5615, 225, 389148081, 455,
    35, 225, 35, 455, 455, 67147089,
    1274913297, 10427516559, 120663101169, 164096181639, 4939349949, 120663075519,
    4939349949, 4939349949, 423137645631, 4939349949, 164096181639, 423137645631,
    10199319201, 4939349949, 4939349949, 10427516559, 11135092913, 954059085,
    53598825, 123918490731, 2897909805, 2783772873, 2897909805, 2897909805,
    954059085, 53598825, 302682231, 11177652105
  ]
def negativeCoefficients : Array ℕ := #[
    5790298008357784993182777344, 5652090058030141278315872256, 5790298008357784993182777344, 5790298008357784993182777344, 3812600661483424397484097536, 214191048397945190869893120,
    206541368098018576910254080, 7627297943004778475185766400, 7627296075271941012093665280, 206543235830856040002355200, 6457507220678074431791169536, 23101305723342725087213125632,
    6457505073938232853842100224, 522612972358322378135044096, 43730995199268433053089792, 522612972358322378135044096, 43730995199268433053089792, 522612972358322378135044096,
    14357030113964389125473697792, 17601959933589000783721922560, 62776736218825446342348767232, 9284550294640352061743431680, 676998458984192337835458560, 17601959933589000783721922560,
    17601959933589000783721922560, 9284550294640352061743431680, 217219791268356570111205703680, 17408531802450660115768934400, 14357030113964389125473697792, 17601959933589000783721922560,
    676998458984192337835458560, 17408531802450660115768934400, 676998458984192337835458560, 17601959933589000783721922560, 17601959933589000783721922560, 619322583038798911254822912,
    23517999305928255471146237952, 24044216161030183254038151168, 139115084150291676235189714944, 189190016635474336656773873664, 22778731099923331503825616896, 139115054577855083069564780544,
    22778731099923331503825616896, 22778731099923331503825616896, 975688982113382699413863923712, 22778731099923331503825616896, 189190016635474336656773873664, 975688982113382699413863923712,
    23518028878364848636771172352, 22778731099923331503825616896, 22778731099923331503825616896, 24044216161030183254038151168, 12837888075192998613733081088, 140794270177540058964169850880,
    7909790459412362863155609600, 142868292782194140794591379456, 213828002086114209400639979520, 12837886436891540567403528192, 213828002086114209400639979520, 213828002086114209400639979520,
    140794270177540058964169850880, 7909790459412362863155609600, 5583501650916435529140535296, 206191287725895844779188551680
  ]
def negativeScales : Array ℕ := #[
    26, 23, 26, 26, 24, 20,
    22, 27, 30, 25, 31, 33,
    29, 23, 20, 23, 20, 23,
    28, 8, 32, 3, 5, 8,
    8, 3, 12, 7, 28, 8,
    5, 7, 5, 8, 8, 26,
    30, 33, 36, 37, 32, 36,
    32, 32, 38, 32, 37, 38,
    33, 32, 32, 33, 33, 29,
    25, 36, 31, 31, 31, 31,
    29, 25, 28, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26225696163043076, 23190843015110887, 26225696163043076, 26225696163043076, 24622833990523865, 20469028654434414,
    22416561234540199, 27623230618420514, 30623230265140853, 25416574280627498, 31383035913500766, 33221961054260367,
    29383035433889775, 23755873403168870, 20176858552817038, 23755873403168870, 20176858552817038, 23755873403168870,
    28535744001900451, 8829722736256263, 32664216681602394, 3906890600547867, 5129283016944967, 8829722736256263,
    8829722736256263, 3906890600547867, 12455070307288020, 7813781192070436, 28535744001900451, 8829722736256263,
    5129283016944967, 7813781192070436, 5129283016944967, 8829722736256263, 8829722736256263, 26000821520658055,
    30247751991077145, 33279676552116655, 36812193611325815, 37255750712871174, 32201674040115381, 36812193304644386,
    32201674040115381, 32201674040115381, 38622336088598473, 32201674040115381, 37255750712871174, 38622336088598473,
    33247753805176220, 32201674040115381, 32201674040115381, 33279676552116655, 33374394545128210, 29829503375548249,
    25675698038344459, 36850600523512377, 31432365546912808, 31374394361019303, 31432365546912808, 31432365546912808,
    29829503375548249, 25675698038344459, 28173228743148940, 33379898127018652
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
noncomputable def negativeCeiling : ℝ := 477037027 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5790298008357784993182777344, coefficient := (-5790298008357784993182777344) }, { argument := 5652090058030141278315872256, coefficient := (-5652090058030141278315872256) }, { argument := 5790298008357784993182777344, coefficient := (-5790298008357784993182777344) }, { argument := 5790298008357784993182777344, coefficient := (-5790298008357784993182777344) }, { argument := 3812600661483424397484097536, coefficient := (-3812600661483424397484097536) }, { argument := 214191048397945190869893120, coefficient := (-214191048397945190869893120) }, { argument := 206541368098018576910254080, coefficient := (-206541368098018576910254080) }, { argument := 7627297943004778475185766400, coefficient := (-7627297943004778475185766400) }, { argument := 7627296075271941012093665280, coefficient := (-7627296075271941012093665280) }, { argument := 206543235830856040002355200, coefficient := (-206543235830856040002355200) }, { argument := 6457507220678074431791169536, coefficient := (-6457507220678074431791169536) }, { argument := 23101305723342725087213125632, coefficient := (-23101305723342725087213125632) }, { argument := 6457505073938232853842100224, coefficient := (-6457505073938232853842100224) }, { argument := 522612972358322378135044096, coefficient := (-522612972358322378135044096) }, { argument := 43730995199268433053089792, coefficient := (-43730995199268433053089792) }, { argument := 522612972358322378135044096, coefficient := (-522612972358322378135044096) }, { argument := 43730995199268433053089792, coefficient := (-43730995199268433053089792) }, { argument := 522612972358322378135044096, coefficient := (-522612972358322378135044096) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 62776736218825446342348767232, coefficient := (-62776736218825446342348767232) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 619322583038798911254822912, coefficient := (-619322583038798911254822912) }, { argument := 23517999305928255471146237952, coefficient := (-23517999305928255471146237952) }, { argument := 24044216161030183254038151168, coefficient := (-24044216161030183254038151168) }, { argument := 139115084150291676235189714944, coefficient := (-139115084150291676235189714944) }, { argument := 189190016635474336656773873664, coefficient := (-189190016635474336656773873664) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 139115054577855083069564780544, coefficient := (-139115054577855083069564780544) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 975688982113382699413863923712, coefficient := (-975688982113382699413863923712) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 189190016635474336656773873664, coefficient := (-189190016635474336656773873664) }, { argument := 975688982113382699413863923712, coefficient := (-975688982113382699413863923712) }, { argument := 23518028878364848636771172352, coefficient := (-23518028878364848636771172352) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 22778731099923331503825616896, coefficient := (-22778731099923331503825616896) }, { argument := 24044216161030183254038151168, coefficient := (-24044216161030183254038151168) }, { argument := 12837888075192998613733081088, coefficient := (-12837888075192998613733081088) }, { argument := 140794270177540058964169850880, coefficient := (-140794270177540058964169850880) }, { argument := 7909790459412362863155609600, coefficient := (-7909790459412362863155609600) }, { argument := 142868292782194140794591379456, coefficient := (-142868292782194140794591379456) }, { argument := 213828002086114209400639979520, coefficient := (-213828002086114209400639979520) }, { argument := 12837886436891540567403528192, coefficient := (-12837886436891540567403528192) }, { argument := 213828002086114209400639979520, coefficient := (-213828002086114209400639979520) }, { argument := 213828002086114209400639979520, coefficient := (-213828002086114209400639979520) }, { argument := 140794270177540058964169850880, coefficient := (-140794270177540058964169850880) }, { argument := 7909790459412362863155609600, coefficient := (-7909790459412362863155609600) }, { argument := 5583501650916435529140535296, coefficient := (-5583501650916435529140535296) }, { argument := 206191287725895844779188551680, coefficient := (-206191287725895844779188551680) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
