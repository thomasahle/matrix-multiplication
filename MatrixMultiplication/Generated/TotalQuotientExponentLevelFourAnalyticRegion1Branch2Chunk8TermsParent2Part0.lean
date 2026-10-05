import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2499191453580588720544541598285824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16616065, 1081, 217993905, 26749, 851, 435982409,
    437, 437, 14789, 805, 26749, 14789,
    4155381, 851, 805, 1081, 1139139777755221, 665,
    217, 2006300876769195, 2191, 1139139542874197, 4389, 1967,
    665, 217, 1106942572197973, 1375371445, 1106780184577963, 694440985,
    1375371445, 2360704843, 1375371445, 2755, 2755, 997573,
    899, 899, 517, 1138977390135211, 665, 217,
    2006025651681365, 2191, 1138977155254187, 4389, 1967, 665,
    217, 1953539329001387, 2360704843, 1953264103913557, 1191947239, 104879333,
    9077, 9077, 12793, 407, 1106942347802709, 1375371445,
    1106779960182699, 694440985, 104877981, 209
  ]
def negativeCoefficients : Array ℕ := #[
    78467148433183411397711626240, 20909580976054626205718020096, 2058894220883739132196301045760, 517400907981947452707448029184, 16460733959872790842799292416, 2058868715382365153242501873664,
    16905618661490974379091165184, 16905618661490974379091165184, 286060863140492013835674189824, 15570964556636423770215546880, 517400907981947452707448029184, 286060863140492013835674189824,
    78492927831813396790933192704, 16460733959872790842799292416, 15570964556636423770215546880, 20909580976054626205718020096, 1282557369655330731000441339904, 205807531531194470701979402240,
    8394780891403984989159686144, 4517787940505423008364872335360, 169520414129641761393998823424, 1282557105202807690300309372928, 169791213513235438329133006848, 152189253579646437545411084288,
    205807531531194470701979402240, 8394780891403984989159686144, 1246306538917832392046282801152, 50742250104406185032800010240, 1246123706711590737621299494912, 51240700498359094512493527040,
    50742250104406185032800010240, 174189272289550749900998705152, 50742250104406185032800010240, 213157800514451416084192952320, 213157800514451416084192952320, 75374484790651529356197756928,
    8694594494668413024486817792, 8694594494668413024486817792, 20000468759704425066338975744, 1282374537449089076575458033664, 205807531531194470701979402240, 8394780891403984989159686144,
    4517168188703925908348097003520, 169520414129641761393998823424, 1282374272996566035875326066688, 169791213513235438329133006848, 152189253579646437545411084288, 205807531531194470701979402240,
    8394780891403984989159686144, 4398979497072127641460173438976, 174189272289550749900998705152, 4398359745270630541443398107136, 175900365337581700292953505792, 1981114587619697263836315779072,
    175574714634271824300927352832, 175574714634271824300927352832, 494905216330558433024515506176, 15745049874660930371373236224, 1246306286271225558520263868416, 50742250104406185032800010240,
    1246123454064983904095280562176, 51240700498359094512493527040, 1981089049061757904795000111104, 16170591763165279840869810176
  ]
def negativeScales : Array ℕ := #[
    23, 10, 27, 14, 9, 28,
    8, 8, 13, 9, 14, 13,
    21, 9, 9, 10, 50, 9,
    7, 50, 11, 50, 12, 10,
    9, 7, 49, 30, 49, 29,
    30, 31, 30, 11, 11, 19,
    9, 9, 9, 50, 9, 7,
    50, 11, 50, 12, 10, 9,
    7, 50, 31, 50, 30, 26,
    13, 13, 13, 8, 49, 30,
    49, 29, 26, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23986075448092397, 10078150807734651, 27699712557708780, 14707197337615895, 9733015321840403, 28699694685548104,
    8771489469857739, 8771489469857739, 13852236885192533, 9652844973024881, 14707197337615895, 13852236885192533,
    21986549349777766, 9733015321840403, 9652844973024881, 10078150807734651, 50016866206617805, 9377210530388555,
    7761551232733342, 50833459401841995, 11097373768990223, 50016865909146213, 12099676554859644, 10941781251345720,
    9377210530388555, 7761551232733342, 49975501816779376, 30357174152252975, 49975290158951051, 29371276855371159,
    30357174152252975, 31136570527844586, 30357174152252975, 11427836603458541, 11427836603458541, 19928062899760805,
    9812177306340859, 9812177306340859, 9014020470314935, 50016660531670275, 9377210530388555, 7761551232733342,
    50833261478828063, 11097373768990223, 50016660234156271, 12099676554859644, 10941781251345720, 9377210530388555,
    7761551232733342, 50795011724301032, 31136570527844586, 50794808455372067, 30150673230962769, 26644155174726127,
    13147999842060191, 13147999842060191, 13643067000128359, 8668884984300449, 49975501524321520, 30357174152252975,
    49975289866450285, 29371276855371159, 26644136576817343, 7707359132166870
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
noncomputable def negativeCeiling : ℝ := 1037881489 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 78467148433183411397711626240, coefficient := (-78467148433183411397711626240) }, { argument := 20909580976054626205718020096, coefficient := (-20909580976054626205718020096) }, { argument := 2058894220883739132196301045760, coefficient := (-2058894220883739132196301045760) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 2058868715382365153242501873664, coefficient := (-2058868715382365153242501873664) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 517400907981947452707448029184, coefficient := (-517400907981947452707448029184) }, { argument := 286060863140492013835674189824, coefficient := (-286060863140492013835674189824) }, { argument := 78492927831813396790933192704, coefficient := (-78492927831813396790933192704) }, { argument := 16460733959872790842799292416, coefficient := (-16460733959872790842799292416) }, { argument := 15570964556636423770215546880, coefficient := (-15570964556636423770215546880) }, { argument := 20909580976054626205718020096, coefficient := (-20909580976054626205718020096) }, { argument := 1282557369655330731000441339904, coefficient := (-1282557369655330731000441339904) }, { argument := 205807531531194470701979402240, coefficient := (-205807531531194470701979402240) }, { argument := 8394780891403984989159686144, coefficient := (-8394780891403984989159686144) }, { argument := 4517787940505423008364872335360, coefficient := (-4517787940505423008364872335360) }, { argument := 169520414129641761393998823424, coefficient := (-169520414129641761393998823424) }, { argument := 1282557105202807690300309372928, coefficient := (-1282557105202807690300309372928) }, { argument := 169791213513235438329133006848, coefficient := (-169791213513235438329133006848) }, { argument := 152189253579646437545411084288, coefficient := (-152189253579646437545411084288) }, { argument := 205807531531194470701979402240, coefficient := (-205807531531194470701979402240) }, { argument := 8394780891403984989159686144, coefficient := (-8394780891403984989159686144) }, { argument := 1246306538917832392046282801152, coefficient := (-1246306538917832392046282801152) }, { argument := 50742250104406185032800010240, coefficient := (-50742250104406185032800010240) }, { argument := 1246123706711590737621299494912, coefficient := (-1246123706711590737621299494912) }, { argument := 51240700498359094512493527040, coefficient := (-51240700498359094512493527040) }, { argument := 50742250104406185032800010240, coefficient := (-50742250104406185032800010240) }, { argument := 174189272289550749900998705152, coefficient := (-174189272289550749900998705152) }, { argument := 50742250104406185032800010240, coefficient := (-50742250104406185032800010240) }, { argument := 213157800514451416084192952320, coefficient := (-213157800514451416084192952320) }, { argument := 213157800514451416084192952320, coefficient := (-213157800514451416084192952320) }, { argument := 75374484790651529356197756928, coefficient := (-75374484790651529356197756928) }, { argument := 8694594494668413024486817792, coefficient := (-8694594494668413024486817792) }, { argument := 8694594494668413024486817792, coefficient := (-8694594494668413024486817792) }, { argument := 20000468759704425066338975744, coefficient := (-20000468759704425066338975744) }, { argument := 1282374537449089076575458033664, coefficient := (-1282374537449089076575458033664) }, { argument := 205807531531194470701979402240, coefficient := (-205807531531194470701979402240) }, { argument := 8394780891403984989159686144, coefficient := (-8394780891403984989159686144) }, { argument := 4517168188703925908348097003520, coefficient := (-4517168188703925908348097003520) }, { argument := 169520414129641761393998823424, coefficient := (-169520414129641761393998823424) }, { argument := 1282374272996566035875326066688, coefficient := (-1282374272996566035875326066688) }, { argument := 169791213513235438329133006848, coefficient := (-169791213513235438329133006848) }, { argument := 152189253579646437545411084288, coefficient := (-152189253579646437545411084288) }, { argument := 205807531531194470701979402240, coefficient := (-205807531531194470701979402240) }, { argument := 8394780891403984989159686144, coefficient := (-8394780891403984989159686144) }, { argument := 4398979497072127641460173438976, coefficient := (-4398979497072127641460173438976) }, { argument := 174189272289550749900998705152, coefficient := (-174189272289550749900998705152) }, { argument := 4398359745270630541443398107136, coefficient := (-4398359745270630541443398107136) }, { argument := 175900365337581700292953505792, coefficient := (-175900365337581700292953505792) }, { argument := 1981114587619697263836315779072, coefficient := (-1981114587619697263836315779072) }, { argument := 175574714634271824300927352832, coefficient := (-175574714634271824300927352832) }, { argument := 175574714634271824300927352832, coefficient := (-175574714634271824300927352832) }, { argument := 494905216330558433024515506176, coefficient := (-494905216330558433024515506176) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 1246306286271225558520263868416, coefficient := (-1246306286271225558520263868416) }, { argument := 50742250104406185032800010240, coefficient := (-50742250104406185032800010240) }, { argument := 1246123454064983904095280562176, coefficient := (-1246123454064983904095280562176) }, { argument := 51240700498359094512493527040, coefficient := (-51240700498359094512493527040) }, { argument := 1981089049061757904795000111104, coefficient := (-1981089049061757904795000111104) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 2311872391069122210978681973637120
def positiveArguments : Array ℕ := #[
    563, 149, 1677883279, 3563, 1677674609, 1799,
    69633097, 5415, 1767, 3924404155, 17841, 1114129333,
    35739, 16017, 5415, 1767, 32577233, 2115,
    427752571, 52335, 1665, 855494333, 855, 855,
    28935, 1575, 52335, 28935, 8147039, 1665,
    1575, 2115
  ]
def positiveCoefficients : Array ℕ := #[
    44605455495530822065165244039168, 11804996214625386301438048600064, 15847159517834035281445800378368, 551347544996726239933197451264, 15845188685406074463712316489728, 556763532668599778635881119744,
    5261328053939373496334068744192, 837930664091291773572344709120, 34178750772144796027293007872, 18532474646806372000004445306880, 690190257527827171389852352512, 5261327019741113747881766944768,
    691292797875315713197184385024, 619627675288560495720602271744, 837930664091291773572344709120, 34178750772144796027293007872, 153841633223834940753909383168, 40910049735759051272056995840,
    4040008808503436396032616824832, 1012306124312505885731963535360, 32205783834533721214172528640, 4039957764444123058037501984768, 33076210424656254219960975360, 33076210424656254219960975360,
    559684297448788722721971240960, 30464930654288655202595635200, 1012306124312505885731963535360, 559684297448788722721971240960, 153893215632927325888578584576, 32205783834533721214172528640,
    30464930654288655202595635200, 40910049735759051272056995840
  ]
def positiveScales : Array ℕ := #[
    9, 7, 30, 11, 30, 10,
    26, 12, 10, 31, 14, 30,
    15, 13, 12, 10, 24, 11,
    28, 15, 10, 29, 9, 9,
    14, 10, 15, 14, 22, 10,
    10, 11
  ]
def negativeArguments : Array ℕ := #[
    694440985, 1191947239, 694440985, 18183, 18183, 209,
    8149, 8149, 7073, 385, 2755, 2755,
    12793, 7073, 1995829, 899, 899, 407,
    385, 517, 149, 207, 207, 149
  ]
def negativeCoefficients : Array ℕ := #[
    51240700498359094512493527040, 175900365337581700292953505792, 51240700498359094512493527040, 175855185424422418269459185664, 175855185424422418269459185664, 16170591763165279840869810176,
    157624584064633810314890051584, 157624584064633810314890051584, 273623434308296708886297051136, 14893966097652231432380088320, 213157800514451416084192952320, 213157800514451416084192952320,
    494905216330558433024515506176, 273623434308296708886297051136, 75400287801113929097645391872, 8694594494668413024486817792, 8694594494668413024486817792, 15745049874660930371373236224,
    14893966097652231432380088320, 20000468759704425066338975744, 11804996214625386301438048600064, 32800459280905435763727195439104, 32800459280905435763727195439104, 11804996214625386301438048600064
  ]
def negativeScales : Array ℕ := #[
    29, 30, 29, 14, 14, 7,
    12, 12, 12, 8, 11, 11,
    13, 12, 20, 9, 9, 8,
    8, 9, 7, 7, 7, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9136991112080229, 7219168520462161, 30643995212990032, 11798876768094178, 30643815781023956, 10812979471199464,
    26053269854313066, 12402745622495688, 10787086324520917, 31869826479075117, 14122908861097359, 30053269570728231,
    15125211646966780, 13967316333526543, 12402745622495688, 10787086324520917, 24957360734912706, 11046441948007312,
    28672201285132855, 15675488477800394, 10701306461953989, 29672183057084367, 9739780609762119, 9739780609762119,
    14820528023597167, 10621136113274016, 15675488477800394, 14820528023597167, 22957844383000395, 10701306461953989,
    10621136113274016, 11046441948007312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29371276855371159, 30150673230962769, 29371276855371159, 14150302627929612, 14150302627929612, 7707359132166870,
    12992407336314480, 12992407336314480, 12788106546471179, 8588714635586389, 11427836603458541, 11427836603458541,
    13643067000128359, 12788106546471179, 20928556694307422, 9812177306340859, 9812177306340859, 8668884984300449,
    8588714635586389, 9014020470314935, 7219168520462162, 7693486957561383, 7693486957561383, 7219168520462162
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 32584097191 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1717925993 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51240700498359094512493527040, coefficient := (-51240700498359094512493527040) }, { argument := 175900365337581700292953505792, coefficient := (-175900365337581700292953505792) }, { argument := 51240700498359094512493527040, coefficient := (-51240700498359094512493527040) }, { argument := 175855185424422418269459185664, coefficient := (-175855185424422418269459185664) }, { argument := 175855185424422418269459185664, coefficient := (-175855185424422418269459185664) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 157624584064633810314890051584, coefficient := (-157624584064633810314890051584) }, { argument := 157624584064633810314890051584, coefficient := (-157624584064633810314890051584) }, { argument := 273623434308296708886297051136, coefficient := (-273623434308296708886297051136) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 213157800514451416084192952320, coefficient := (-213157800514451416084192952320) }, { argument := 213157800514451416084192952320, coefficient := (-213157800514451416084192952320) }, { argument := 494905216330558433024515506176, coefficient := (-494905216330558433024515506176) }, { argument := 273623434308296708886297051136, coefficient := (-273623434308296708886297051136) }, { argument := 75400287801113929097645391872, coefficient := (-75400287801113929097645391872) }, { argument := 8694594494668413024486817792, coefficient := (-8694594494668413024486817792) }, { argument := 8694594494668413024486817792, coefficient := (-8694594494668413024486817792) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 20000468759704425066338975744, coefficient := (-20000468759704425066338975744) }, { argument := 44605455495530822065165244039168, coefficient := 44605455495530822065165244039168 }, { argument := 11804996214625386301438048600064, coefficient := 11804996214625386301438048600064 }, { argument := 11804996214625386301438048600064, coefficient := (-11804996214625386301438048600064) }, { argument := 15847159517834035281445800378368, coefficient := 15847159517834035281445800378368 }, { argument := 551347544996726239933197451264, coefficient := 551347544996726239933197451264 }, { argument := 15845188685406074463712316489728, coefficient := 15845188685406074463712316489728 }, { argument := 556763532668599778635881119744, coefficient := 556763532668599778635881119744 }, { argument := 32800459280905435763727195439104, coefficient := (-32800459280905435763727195439104) }, { argument := 5261328053939373496334068744192, coefficient := 5261328053939373496334068744192 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 18532474646806372000004445306880, coefficient := 18532474646806372000004445306880 }, { argument := 690190257527827171389852352512, coefficient := 690190257527827171389852352512 }, { argument := 5261327019741113747881766944768, coefficient := 5261327019741113747881766944768 }, { argument := 691292797875315713197184385024, coefficient := 691292797875315713197184385024 }, { argument := 619627675288560495720602271744, coefficient := 619627675288560495720602271744 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 32800459280905435763727195439104, coefficient := (-32800459280905435763727195439104) }, { argument := 153841633223834940753909383168, coefficient := 153841633223834940753909383168 }, { argument := 40910049735759051272056995840, coefficient := 40910049735759051272056995840 }, { argument := 4040008808503436396032616824832, coefficient := 4040008808503436396032616824832 }, { argument := 1012306124312505885731963535360, coefficient := 1012306124312505885731963535360 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 4039957764444123058037501984768, coefficient := 4039957764444123058037501984768 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 559684297448788722721971240960, coefficient := 559684297448788722721971240960 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 1012306124312505885731963535360, coefficient := 1012306124312505885731963535360 }, { argument := 559684297448788722721971240960, coefficient := 559684297448788722721971240960 }, { argument := 153893215632927325888578584576, coefficient := 153893215632927325888578584576 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 40910049735759051272056995840, coefficient := 40910049735759051272056995840 }, { argument := 11804996214625386301438048600064, coefficient := (-11804996214625386301438048600064) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8
