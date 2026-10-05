import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-209864164376346607850196043825152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    89421194943, 2421479745, 44070984503, 157661037261, 11017742463, 389148081,
    189234767, 389148081, 189234767, 1326551373, 4745649951, 331637733,
    455, 455, 141453, 159008967, 728700597, 2766133827,
    11467446237, 345173967, 1383066711, 345173967, 345173967, 29569903173,
    345173967, 11467446237, 29569903173, 1272072141, 345173967, 345173967,
    728700597, 11135091233, 7632470811, 428790495, 123918464131, 23183272763,
    2783772453, 23183272763, 23183272763, 7632470811, 428790495, 6806267379,
    7553113613, 6806267379, 7553113613, 1326551373, 4745649951, 331637733,
    15, 15, 4216691, 35, 35, 5,
    1185331, 189234767, 7553113613, 189234767, 4740783, 302682231,
    11177652105, 89421194943, 2421479745, 1326551373
  ]
def negativeCoefficients : Array ℕ := #[
    206191237234851472026932084736, 5583552141960808281397002240, 50810385762703796186988412928, 181770800296828284238861172736, 50810368871250832192073367552, 14357030113964389125473697792,
    6981530633394115651456466944, 14357030113964389125473697792, 6981530633394115651456466944, 6117638419589754724854792192, 21885447527377318503675592704, 6117636385836220598376726528,
    17601959933589000783721922560, 17601959933589000783721922560, 1335985812202719848825880576, 5866395439347855320986681344, 6721076709609181133590757376, 12756540695074943024505028608,
    52884261478240662077464117248, 6367335830156066337085980672, 12756538827342105561412927488, 6367335830156066337085980672, 6367335830156066337085980672, 272734218058351508105182838784,
    6367335830156066337085980672, 52884261478240662077464117248, 272734218058351508105182838784, 5866397307080692784078782464, 6367335830156066337085980672, 6367335830156066337085980672,
    6721076709609181133590757376, 12837886138284870874230161408, 140794235700575385201017880576, 7909788522504235123652689920, 142868262114482118252461817856, 213827949725031156176077717504,
    12837884499983412827900608512, 213827949725031156176077717504, 213827949725031156176077717504, 140794235700575385201017880576, 7909788522504235123652689920, 62776736218825446342348767232,
    69665176889331344859467874304, 62776736218825446342348767232, 69665176889331344859467874304, 6117638419589754724854792192, 21885447527377318503675592704, 6117636385836220598376726528,
    9284550294640352061743431680, 9284550294640352061743431680, 39825520494036174291569999872, 676998458984192337835458560, 676998458984192337835458560, 773712524553362671811952640,
    43730995199268433053089792, 6981530633394115651456466944, 69665176889331344859467874304, 6981530633394115651456466944, 43726005354996494619377664, 5583501650916435529140535296,
    206191287725895844779188551680, 206191237234851472026932084736, 5583552141960808281397002240, 6117638419589754724854792192
  ]
def negativeScales : Array ℕ := #[
    36, 31, 35, 37, 33, 28,
    27, 28, 27, 30, 32, 28,
    8, 8, 17, 27, 29, 31,
    33, 28, 30, 28, 28, 34,
    28, 33, 34, 30, 28, 28,
    29, 33, 32, 28, 36, 34,
    31, 34, 34, 32, 28, 32,
    32, 32, 32, 30, 32, 28,
    3, 3, 22, 5, 5, 2,
    20, 27, 32, 27, 22, 28,
    33, 36, 31, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36379897773738991, 31173241789236239, 35359110074255283, 37198035215014887, 33359109594644292, 28535744001900451,
    27495601930073321, 28535744001900451, 27495601930073321, 30305033401499490, 32143958542259094, 28305032921888498,
    8829722736256263, 8829722736256263, 17109963248832529, 27244532884870520, 29440750931746092, 31365223810503127,
    33416825092500591, 28362748419744787, 30365223599272734, 28362748419744787, 28362748419744787, 34783410468676387,
    28362748419744787, 33416825092500591, 34783410468676387, 30244533344193199, 28362748419744787, 28362748419744787,
    29440750931746092, 33374394327462504, 32829503022268580, 28675697685064798, 36850600213827412, 34432365193633147,
    31374394143353570, 34432365193633147, 34432365193633147, 32829503022268580, 28675697685064798, 32664216681602394,
    32814424342737678, 32664216681602394, 32814424342737678, 30305033401499490, 32143958542259094, 28305032921888498,
    3906890600547867, 3906890600547867, 22007679873819777, 5129283016944967, 5129283016944967, 2321928094887363,
    20176858552817038, 27495601930073321, 32814424342737678, 27495601930073321, 22176693927377151, 28173228743148940,
    33379898127018652, 36379897773738991, 31173241789236239, 30305033401499490
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
noncomputable def negativeCeiling : ℝ := 1345579877 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 206191237234851472026932084736, coefficient := (-206191237234851472026932084736) }, { argument := 5583552141960808281397002240, coefficient := (-5583552141960808281397002240) }, { argument := 50810385762703796186988412928, coefficient := (-50810385762703796186988412928) }, { argument := 181770800296828284238861172736, coefficient := (-181770800296828284238861172736) }, { argument := 50810368871250832192073367552, coefficient := (-50810368871250832192073367552) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }, { argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 1335985812202719848825880576, coefficient := (-1335985812202719848825880576) }, { argument := 5866395439347855320986681344, coefficient := (-5866395439347855320986681344) }, { argument := 6721076709609181133590757376, coefficient := (-6721076709609181133590757376) }, { argument := 12756540695074943024505028608, coefficient := (-12756540695074943024505028608) }, { argument := 52884261478240662077464117248, coefficient := (-52884261478240662077464117248) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 12756538827342105561412927488, coefficient := (-12756538827342105561412927488) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 272734218058351508105182838784, coefficient := (-272734218058351508105182838784) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 52884261478240662077464117248, coefficient := (-52884261478240662077464117248) }, { argument := 272734218058351508105182838784, coefficient := (-272734218058351508105182838784) }, { argument := 5866397307080692784078782464, coefficient := (-5866397307080692784078782464) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 6367335830156066337085980672, coefficient := (-6367335830156066337085980672) }, { argument := 6721076709609181133590757376, coefficient := (-6721076709609181133590757376) }, { argument := 12837886138284870874230161408, coefficient := (-12837886138284870874230161408) }, { argument := 140794235700575385201017880576, coefficient := (-140794235700575385201017880576) }, { argument := 7909788522504235123652689920, coefficient := (-7909788522504235123652689920) }, { argument := 142868262114482118252461817856, coefficient := (-142868262114482118252461817856) }, { argument := 213827949725031156176077717504, coefficient := (-213827949725031156176077717504) }, { argument := 12837884499983412827900608512, coefficient := (-12837884499983412827900608512) }, { argument := 213827949725031156176077717504, coefficient := (-213827949725031156176077717504) }, { argument := 213827949725031156176077717504, coefficient := (-213827949725031156176077717504) }, { argument := 140794235700575385201017880576, coefficient := (-140794235700575385201017880576) }, { argument := 7909788522504235123652689920, coefficient := (-7909788522504235123652689920) }, { argument := 62776736218825446342348767232, coefficient := (-62776736218825446342348767232) }, { argument := 69665176889331344859467874304, coefficient := (-69665176889331344859467874304) }, { argument := 62776736218825446342348767232, coefficient := (-62776736218825446342348767232) }, { argument := 69665176889331344859467874304, coefficient := (-69665176889331344859467874304) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }, { argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 39825520494036174291569999872, coefficient := (-39825520494036174291569999872) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 43730995199268433053089792, coefficient := (-43730995199268433053089792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 69665176889331344859467874304, coefficient := (-69665176889331344859467874304) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 43726005354996494619377664, coefficient := (-43726005354996494619377664) }, { argument := 5583501650916435529140535296, coefficient := (-5583501650916435529140535296) }, { argument := 206191287725895844779188551680, coefficient := (-206191287725895844779188551680) }, { argument := 206191237234851472026932084736, coefficient := (-206191237234851472026932084736) }, { argument := 5583552141960808281397002240, coefficient := (-5583552141960808281397002240) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-312270159872269147947987294486528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4745649951, 331637733, 302682231, 11177652105, 89421194943, 2421479745,
    113641234287, 406544012469, 28410299127, 455, 455, 1326551373,
    4745649951, 331637733, 455, 455, 47, 99650007,
    3679942185, 29439530271, 797207265, 44070984503, 157661037261, 11017742463,
    15, 15, 113641234287, 406544012469, 28410299127, 5615,
    5615, 555, 225, 225, 39, 306400619,
    206683365, 11611425, 2476872881, 627791045, 306400521, 627791045,
    627791045, 206683365, 11611425, 389148081, 189234767, 389148081,
    189234767, 2108345, 455, 455, 555, 5,
    5598315, 206738325, 1653906195, 44786925, 1326551373, 4745649951,
    331637733, 35, 35, 1326551373
  ]
def negativeCoefficients : Array ℕ := #[
    21885447527377318503675592704, 6117636385836220598376726528, 5583501650916435529140535296, 206191287725895844779188551680, 206191237234851472026932084736, 5583552141960808281397002240,
    262038845639094494047946932224, 937426669089328475907437887488, 262038758526651448963803119616, 17601959933589000783721922560, 17601959933589000783721922560, 6117638419589754724854792192,
    21885447527377318503675592704, 6117636385836220598376726528, 17601959933589000783721922560, 17601959933589000783721922560, 909112216350201139379044352, 3676436352144730669002522624,
    135765903385485056858306641920, 135765870139840550015267241984, 3676469597789237512041922560, 50810385762703796186988412928, 181770800296828284238861172736, 50810368871250832192073367552,
    9284550294640352061743431680, 9284550294640352061743431680, 262038845639094494047946932224, 937426669089328475907437887488, 262038758526651448963803119616, 217219791268356570111205703680,
    217219791268356570111205703680, 10735261278177907071390842880, 17408531802450660115768934400, 17408531802450660115768934400, 24139830766064915360532922368, 5652093802719188241354850304,
    3812635138448098160636067840, 214192985306072930372812800, 22845120069459326734170062848, 5790350369440838217745039360, 5652091994938269017818791936, 5790350369440838217745039360,
    5790350369440838217745039360, 3812635138448098160636067840, 214192985306072930372812800, 14357030113964389125473697792, 6981530633394115651456466944, 14357030113964389125473697792,
    6981530633394115651456466944, 39825511049303208552279572480, 17601959933589000783721922560, 17601959933589000783721922560, 10735261278177907071390842880, 773712524553362671811952640,
    206541368098018576910254080, 7627297943004778475185766400, 7627296075271941012093665280, 206543235830856040002355200, 6117638419589754724854792192, 21885447527377318503675592704,
    6117636385836220598376726528, 676998458984192337835458560, 676998458984192337835458560, 6117638419589754724854792192
  ]
def negativeScales : Array ℕ := #[
    32, 28, 28, 33, 36, 31,
    36, 38, 34, 8, 8, 30,
    32, 28, 8, 8, 5, 26,
    31, 34, 29, 35, 37, 33,
    3, 3, 36, 38, 34, 12,
    12, 9, 7, 7, 5, 28,
    27, 23, 31, 29, 28, 29,
    29, 27, 23, 28, 27, 28,
    27, 21, 8, 8, 9, 2,
    22, 27, 30, 25, 30, 32,
    28, 5, 5, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32143958542259094, 28305032921888498, 28173228743148940, 33379898127018652, 36379897773738991, 31173241789236239,
    36725695450103183, 38564620590733874, 34725694970492191, 8829722736256263, 8829722736256263, 30305033401499490,
    32143958542259094, 28305032921888498, 8829722736256263, 8829722736256263, 5554588851679165, 26570366570621658,
    31777035954890454, 34777035601610790, 29570379616708957, 35359110074255283, 37198035215014887, 33359109594644292,
    3906890600547867, 3906890600547867, 36725695450103183, 38564620590733874, 34725694970492191, 12455070307288020,
    12455070307288020, 9116343961237469, 7813781192070436, 7813781192070436, 5285402218862249, 28190843970941822,
    27622847036611167, 23469041700521713, 31205872681933909, 29225709209130375, 28190843509506277, 29225709209130375,
    29225709209130375, 27622847036611167, 23469041700521713, 28535744001900451, 27495601930073321, 28535744001900451,
    27495601930073321, 21007679531680594, 8829722736256263, 8829722736256263, 9116343961237469, 2321928094887363,
    22416561234540199, 27623230618420514, 30623230265140853, 25416574280627498, 30305033401499490, 32143958542259094,
    28305032921888498, 5129283016944967, 5129283016944967, 30305033401499490
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
noncomputable def negativeCeiling : ℝ := 381394193 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 5583501650916435529140535296, coefficient := (-5583501650916435529140535296) }, { argument := 206191287725895844779188551680, coefficient := (-206191287725895844779188551680) }, { argument := 206191237234851472026932084736, coefficient := (-206191237234851472026932084736) }, { argument := 5583552141960808281397002240, coefficient := (-5583552141960808281397002240) }, { argument := 262038845639094494047946932224, coefficient := (-262038845639094494047946932224) }, { argument := 937426669089328475907437887488, coefficient := (-937426669089328475907437887488) }, { argument := 262038758526651448963803119616, coefficient := (-262038758526651448963803119616) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }, { argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 909112216350201139379044352, coefficient := (-909112216350201139379044352) }, { argument := 3676436352144730669002522624, coefficient := (-3676436352144730669002522624) }, { argument := 135765903385485056858306641920, coefficient := (-135765903385485056858306641920) }, { argument := 135765870139840550015267241984, coefficient := (-135765870139840550015267241984) }, { argument := 3676469597789237512041922560, coefficient := (-3676469597789237512041922560) }, { argument := 50810385762703796186988412928, coefficient := (-50810385762703796186988412928) }, { argument := 181770800296828284238861172736, coefficient := (-181770800296828284238861172736) }, { argument := 50810368871250832192073367552, coefficient := (-50810368871250832192073367552) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 262038845639094494047946932224, coefficient := (-262038845639094494047946932224) }, { argument := 937426669089328475907437887488, coefficient := (-937426669089328475907437887488) }, { argument := 262038758526651448963803119616, coefficient := (-262038758526651448963803119616) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 217219791268356570111205703680, coefficient := (-217219791268356570111205703680) }, { argument := 10735261278177907071390842880, coefficient := (-10735261278177907071390842880) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 17408531802450660115768934400, coefficient := (-17408531802450660115768934400) }, { argument := 24139830766064915360532922368, coefficient := (-24139830766064915360532922368) }, { argument := 5652093802719188241354850304, coefficient := (-5652093802719188241354850304) }, { argument := 3812635138448098160636067840, coefficient := (-3812635138448098160636067840) }, { argument := 214192985306072930372812800, coefficient := (-214192985306072930372812800) }, { argument := 22845120069459326734170062848, coefficient := (-22845120069459326734170062848) }, { argument := 5790350369440838217745039360, coefficient := (-5790350369440838217745039360) }, { argument := 5652091994938269017818791936, coefficient := (-5652091994938269017818791936) }, { argument := 5790350369440838217745039360, coefficient := (-5790350369440838217745039360) }, { argument := 5790350369440838217745039360, coefficient := (-5790350369440838217745039360) }, { argument := 3812635138448098160636067840, coefficient := (-3812635138448098160636067840) }, { argument := 214192985306072930372812800, coefficient := (-214192985306072930372812800) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 14357030113964389125473697792, coefficient := (-14357030113964389125473697792) }, { argument := 6981530633394115651456466944, coefficient := (-6981530633394115651456466944) }, { argument := 39825511049303208552279572480, coefficient := (-39825511049303208552279572480) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 17601959933589000783721922560, coefficient := (-17601959933589000783721922560) }, { argument := 10735261278177907071390842880, coefficient := (-10735261278177907071390842880) }, { argument := 773712524553362671811952640, coefficient := (-773712524553362671811952640) }, { argument := 206541368098018576910254080, coefficient := (-206541368098018576910254080) }, { argument := 7627297943004778475185766400, coefficient := (-7627297943004778475185766400) }, { argument := 7627296075271941012093665280, coefficient := (-7627296075271941012093665280) }, { argument := 206543235830856040002355200, coefficient := (-206543235830856040002355200) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }, { argument := 21885447527377318503675592704, coefficient := (-21885447527377318503675592704) }, { argument := 6117636385836220598376726528, coefficient := (-6117636385836220598376726528) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 676998458984192337835458560, coefficient := (-676998458984192337835458560) }, { argument := 6117638419589754724854792192, coefficient := (-6117638419589754724854792192) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
