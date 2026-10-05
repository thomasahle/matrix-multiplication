import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11

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
def constantNumerator : ℤ := 126260026744202694400975630250278912
def positiveArguments : Array ℕ := #[
    16907, 5, 21, 91, 3, 3,
    7, 91, 91, 3, 1123, 45,
    21, 91, 7, 45, 7, 91,
    91, 3, 889
  ]
def positiveCoefficients : Array ℕ := #[
    1339510543628667155694047568330752, 193428131138340667952988160, 3249592603124123221610201088, 7040783973435600313488769024, 232113757366008801543585792, 3713820117856140824697372672,
    270799383593676935134183424, 7040783973435600313488769024, 7040783973435600313488769024, 3713820117856140824697372672, 86887916507342628044482281472, 6963412720980264046307573760,
    3249592603124123221610201088, 7040783973435600313488769024, 270799383593676935134183424, 6963412720980264046307573760, 270799383593676935134183424, 7040783973435600313488769024,
    7040783973435600313488769024, 232113757366008801543585792, 70433836475180996120660571848704
  ]
def positiveScales : Array ℕ := #[
    14, 2, 4, 6, 1, 1,
    2, 6, 6, 1, 10, 5,
    4, 6, 2, 5, 2, 6,
    6, 1, 9
  ]
def negativeArguments : Array ℕ := #[
    5658114747, 35960856699, 65398693765, 35960856699, 191482606165, 191482514859,
    6395, 10422847925, 10422842955, 457, 12157585005, 22109878675,
    12157585005, 346336346765, 346336181619, 13079, 191482606165, 191482514859,
    51139, 4029, 963704515607931, 281438825, 963695799478917, 142101725,
    237131213, 6395, 3967211949, 7214802515, 3967211949, 11018439235,
    11018433981, 837, 10422847925, 10422842955, 4029, 837,
    13996395785, 13996389111, 12873, 457, 3705347, 1,
    889
  ]
def negativeCoefficients : Array ℕ := #[
    104373794677590868993247281152, 82920090024724584876314984448, 301598241659464888422561218560, 82920090024724584876314984448, 1766115315246336901342633656320, 1766114473097129704280473731072,
    494789159451875428623743713280, 96133804095834823556752998400, 96133758255675800388517232640, 282869298976709392814449885184, 112133929570801929725977559040, 407855273418493443418410188800,
    112133929570801929725977559040, 3194388976098739994185821061120, 3194387452895741595767015473152, 505969305431671519231426428928, 1766115315246336901342633656320, 1766114473097129704280473731072,
    7913376958626882734758289211392, 311728776142549820473035718656, 2170069648693571199028206501888, 1297907494295132399520972800, 2170050021715881417243849916416, 1310657076753827216805068800,
    2239640984626845380806753386496, 494789159451875428623743713280, 4573883969335341870401716224, 16636201942070127297329889280, 4573883969335341870401716224, 101627164329882527759996026880,
    101627115870285846125003931648, 16189934576279113907665108992, 96133804095834823556752998400, 96133758255675800388517232640, 311728776142549820473035718656, 16189934576279113907665108992,
    129093965500121048776211169280, 129093903943336074807437426688, 498000066428771883711763316736, 282869298976709392814449885184, 34996012960403182567265665024, 158456325028528675187087900672,
    70433836475180996120660571848704
  ]
def negativeScales : Array ℕ := #[
    32, 35, 35, 35, 37, 37,
    12, 33, 33, 8, 33, 34,
    33, 38, 38, 13, 37, 37,
    15, 11, 49, 28, 49, 27,
    27, 12, 31, 32, 31, 33,
    33, 9, 33, 33, 11, 9,
    33, 33, 13, 8, 21, 0,
    9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14045333068328068, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924,
    2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661,
    4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 9796039608792852
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32397674288982931, 35065708339600194, 35928542776565779, 35065708339600194, 37478422390798020, 37478421702867417,
    12642728643786688, 33279030480414910, 33279029792484306, 8836050356382083, 33501137627710497, 34363972057453541,
    33501137627710497, 38333382844943162, 38333382157012559, 13674964618422665, 37478422390798020, 37478421702867417,
    15642136329173682, 11976206106266856, 49775584193925365, 28068246123818555, 49775571145555383, 27082348826936738,
    27821110333815376, 12642728643786688, 31885478333124769, 32748312759726197, 31885478333124769, 33359200829098894,
    33359200141168291, 9709083812639846, 33279030480414910, 33279029792484306, 11976206106266856, 9709083812639846,
    33704336315227715, 33704335627297111, 13652060686491993, 8836050356382083, 21821177225323884, 0,
    9796039609425563
  ]

abbrev PositiveTerm := Fin 21
abbrev NegativeTerm := Fin 43
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
noncomputable def positiveFloor : ℝ := 234784341993 / 1000000000000
noncomputable def negativeCeiling : ℝ := 20610892659 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 104373794677590868993247281152, coefficient := (-104373794677590868993247281152) }, { argument := 82920090024724584876314984448, coefficient := (-82920090024724584876314984448) }, { argument := 301598241659464888422561218560, coefficient := (-301598241659464888422561218560) }, { argument := 82920090024724584876314984448, coefficient := (-82920090024724584876314984448) }, { argument := 1766115315246336901342633656320, coefficient := (-1766115315246336901342633656320) }, { argument := 1766114473097129704280473731072, coefficient := (-1766114473097129704280473731072) }, { argument := 494789159451875428623743713280, coefficient := (-494789159451875428623743713280) }, { argument := 96133804095834823556752998400, coefficient := (-96133804095834823556752998400) }, { argument := 96133758255675800388517232640, coefficient := (-96133758255675800388517232640) }, { argument := 282869298976709392814449885184, coefficient := (-282869298976709392814449885184) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 407855273418493443418410188800, coefficient := (-407855273418493443418410188800) }, { argument := 112133929570801929725977559040, coefficient := (-112133929570801929725977559040) }, { argument := 3194388976098739994185821061120, coefficient := (-3194388976098739994185821061120) }, { argument := 3194387452895741595767015473152, coefficient := (-3194387452895741595767015473152) }, { argument := 505969305431671519231426428928, coefficient := (-505969305431671519231426428928) }, { argument := 1766115315246336901342633656320, coefficient := (-1766115315246336901342633656320) }, { argument := 1766114473097129704280473731072, coefficient := (-1766114473097129704280473731072) }, { argument := 7913376958626882734758289211392, coefficient := (-7913376958626882734758289211392) }, { argument := 311728776142549820473035718656, coefficient := (-311728776142549820473035718656) }, { argument := 2170069648693571199028206501888, coefficient := (-2170069648693571199028206501888) }, { argument := 1297907494295132399520972800, coefficient := (-1297907494295132399520972800) }, { argument := 2170050021715881417243849916416, coefficient := (-2170050021715881417243849916416) }, { argument := 1310657076753827216805068800, coefficient := (-1310657076753827216805068800) }, { argument := 2239640984626845380806753386496, coefficient := (-2239640984626845380806753386496) }, { argument := 494789159451875428623743713280, coefficient := (-494789159451875428623743713280) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 16636201942070127297329889280, coefficient := (-16636201942070127297329889280) }, { argument := 4573883969335341870401716224, coefficient := (-4573883969335341870401716224) }, { argument := 101627164329882527759996026880, coefficient := (-101627164329882527759996026880) }, { argument := 101627115870285846125003931648, coefficient := (-101627115870285846125003931648) }, { argument := 16189934576279113907665108992, coefficient := (-16189934576279113907665108992) }, { argument := 96133804095834823556752998400, coefficient := (-96133804095834823556752998400) }, { argument := 96133758255675800388517232640, coefficient := (-96133758255675800388517232640) }, { argument := 311728776142549820473035718656, coefficient := (-311728776142549820473035718656) }, { argument := 16189934576279113907665108992, coefficient := (-16189934576279113907665108992) }, { argument := 129093965500121048776211169280, coefficient := (-129093965500121048776211169280) }, { argument := 129093903943336074807437426688, coefficient := (-129093903943336074807437426688) }, { argument := 498000066428771883711763316736, coefficient := (-498000066428771883711763316736) }, { argument := 282869298976709392814449885184, coefficient := (-282869298976709392814449885184) }, { argument := 34996012960403182567265665024, coefficient := (-34996012960403182567265665024) }, { argument := 1339510543628667155694047568330752, coefficient := 1339510543628667155694047568330752 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 86887916507342628044482281472, coefficient := 86887916507342628044482281472 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 70433836475180996120660571848704, coefficient := 70433836475180996120660571848704 }, { argument := 70433836475180996120660571848704, coefficient := (-70433836475180996120660571848704) }] }

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
def constantNumerator : ℤ := (-68679195914223224651110631048478720)
def positiveArguments : Array ℕ := #[
    16871678035, 2545, 16871518125, 1285, 24618121999, 4085,
    1333, 167692614979, 13459, 49236241567, 26961, 12083,
    4085, 1333, 1836606407, 13207, 30586475489, 326803,
    10397, 61172874303, 5339, 5339, 180683, 9835,
    326803, 180683, 229586695, 10397, 9835, 13207,
    14865891, 944596407, 51867, 7742928655, 53223, 1695,
    51867, 29493, 53223, 830889, 1017, 472298431,
    51867, 1695, 1017, 1695, 26103, 29493,
    14865881
  ]
def positiveCoefficients : Array ℕ := #[
    318696987449007987680630737469440, 196909837498830799976141946880, 318693966834510884940766248960000, 198844118810214206655671828480, 232511588398546938969229107396608, 1264246265120194605740730613760,
    51567939761481622076266643456, 791905984401593813866653505552384, 1041339686796370819991707058176, 232511576918474019113121592901632, 1043003168724160549736102756352, 934876843417828116350382374912,
    1264246265120194605740730613760, 51567939761481622076266643456, 8673128538640446145290957750272, 510921065588813040331022925824, 288881093356735083421677742194688, 12642578708080629061808077930496,
    402214455889065584941443579904, 288880731269285009391630982053888, 413085116859040330480401514496, 413085116859040330480401514496, 6989835003693761381549951942656, 380473133949116093863527710720,
    12642578708080629061808077930496, 6989835003693761381549951942656, 8673540107046527683480266997760, 402214455889065584941443579904, 380473133949116093863527710720, 510921065588813040331022925824,
    70202185396393512955476443136, 4460730412255893918221988790272, 1003253687775231542471763689472, 36564946759622942554810356858880, 1029482542357590537046188883968, 32786068227948743218031493120,
    1003253687775231542471763689472, 570477587166308131993747980288, 1029482542357590537046188883968, 16071730645340473925479037927424, 629492509976615869786204667904, 4460732560932643623910561021952,
    1003253687775231542471763689472, 32786068227948743218031493120, 629492509976615869786204667904, 32786068227948743218031493120, 1009810901420821291115369988096, 570477587166308131993747980288,
    70202138172728684259024306176
  ]
def positiveScales : Array ℕ := #[
    33, 11, 33, 10, 34, 11,
    10, 37, 13, 35, 14, 13,
    11, 10, 30, 13, 34, 18,
    13, 35, 12, 12, 17, 13,
    18, 17, 27, 13, 13, 13,
    23, 29, 15, 32, 15, 10,
    15, 14, 15, 19, 9, 28,
    15, 10, 9, 10, 14, 14,
    23
  ]
def negativeArguments : Array ℕ := #[
    4025, 249, 4025, 887
  ]
def negativeCoefficients : Array ℕ := #[
    637786708239827917628028800204800, 1262579997827316483890716392554496, 637786708239827917628028800204800, 70275380150152467445473483948032
  ]
def negativeScales : Array ℕ := #[
    11, 7, 11, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    33973884417237183, 11313449940963057, 33973870743288854, 10327552644081240, 34519001658459166, 11996120361661050,
    10380461065088972, 37287028199164297, 13716283601628156, 35519001587227255, 14718586387497221, 13560691074922909,
    11996120361661050, 10380461065088972, 30774395337510704, 13689015171895098, 34832174822039165, 18318061701694144,
    13343879685849875, 35832173013744655, 12382353833664511, 12382353833664511, 17463101247548868, 13263709337165892,
    18318061701694144, 17463101247548868, 27774463796499618, 13343879685849875, 13263709337165892, 13689015171895098,
    23825502599153509, 29815122806905366, 15662529305827180, 32850232202792329, 15699762212023501, 10727069558015321,
    15662529305827180, 14848084958881724, 15699762212023501, 19664296232001286, 9990103962611722, 28815123501832935,
    15662529305827180, 10727069558015321, 9990103962611722, 10727069558015321, 14671928003828954, 14848084958881724,
    23825501628679877
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11974773083633342, 7960001944397948, 11974773083633342, 9792790294858386
  ]

abbrev PositiveTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 1096886793681 / 1000000000000
noncomputable def negativeCeiling : ℝ := 7828012529 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 318696987449007987680630737469440, coefficient := 318696987449007987680630737469440 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 318693966834510884940766248960000, coefficient := 318693966834510884940766248960000 }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 637786708239827917628028800204800, coefficient := (-637786708239827917628028800204800) }, { argument := 232511588398546938969229107396608, coefficient := 232511588398546938969229107396608 }, { argument := 1264246265120194605740730613760, coefficient := 1264246265120194605740730613760 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 791905984401593813866653505552384, coefficient := 791905984401593813866653505552384 }, { argument := 1041339686796370819991707058176, coefficient := 1041339686796370819991707058176 }, { argument := 232511576918474019113121592901632, coefficient := 232511576918474019113121592901632 }, { argument := 1043003168724160549736102756352, coefficient := 1043003168724160549736102756352 }, { argument := 934876843417828116350382374912, coefficient := 934876843417828116350382374912 }, { argument := 1264246265120194605740730613760, coefficient := 1264246265120194605740730613760 }, { argument := 51567939761481622076266643456, coefficient := 51567939761481622076266643456 }, { argument := 1262579997827316483890716392554496, coefficient := (-1262579997827316483890716392554496) }, { argument := 8673128538640446145290957750272, coefficient := 8673128538640446145290957750272 }, { argument := 510921065588813040331022925824, coefficient := 510921065588813040331022925824 }, { argument := 288881093356735083421677742194688, coefficient := 288881093356735083421677742194688 }, { argument := 12642578708080629061808077930496, coefficient := 12642578708080629061808077930496 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 288880731269285009391630982053888, coefficient := 288880731269285009391630982053888 }, { argument := 413085116859040330480401514496, coefficient := 413085116859040330480401514496 }, { argument := 413085116859040330480401514496, coefficient := 413085116859040330480401514496 }, { argument := 6989835003693761381549951942656, coefficient := 6989835003693761381549951942656 }, { argument := 380473133949116093863527710720, coefficient := 380473133949116093863527710720 }, { argument := 12642578708080629061808077930496, coefficient := 12642578708080629061808077930496 }, { argument := 6989835003693761381549951942656, coefficient := 6989835003693761381549951942656 }, { argument := 8673540107046527683480266997760, coefficient := 8673540107046527683480266997760 }, { argument := 402214455889065584941443579904, coefficient := 402214455889065584941443579904 }, { argument := 380473133949116093863527710720, coefficient := 380473133949116093863527710720 }, { argument := 510921065588813040331022925824, coefficient := 510921065588813040331022925824 }, { argument := 637786708239827917628028800204800, coefficient := (-637786708239827917628028800204800) }, { argument := 70202185396393512955476443136, coefficient := 70202185396393512955476443136 }, { argument := 4460730412255893918221988790272, coefficient := 4460730412255893918221988790272 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 36564946759622942554810356858880, coefficient := 36564946759622942554810356858880 }, { argument := 1029482542357590537046188883968, coefficient := 1029482542357590537046188883968 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 570477587166308131993747980288, coefficient := 570477587166308131993747980288 }, { argument := 1029482542357590537046188883968, coefficient := 1029482542357590537046188883968 }, { argument := 16071730645340473925479037927424, coefficient := 16071730645340473925479037927424 }, { argument := 629492509976615869786204667904, coefficient := 629492509976615869786204667904 }, { argument := 4460732560932643623910561021952, coefficient := 4460732560932643623910561021952 }, { argument := 1003253687775231542471763689472, coefficient := 1003253687775231542471763689472 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 629492509976615869786204667904, coefficient := 629492509976615869786204667904 }, { argument := 32786068227948743218031493120, coefficient := 32786068227948743218031493120 }, { argument := 1009810901420821291115369988096, coefficient := 1009810901420821291115369988096 }, { argument := 570477587166308131993747980288, coefficient := 570477587166308131993747980288 }, { argument := 70202138172728684259024306176, coefficient := 70202138172728684259024306176 }, { argument := 70275380150152467445473483948032, coefficient := (-70275380150152467445473483948032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk11
