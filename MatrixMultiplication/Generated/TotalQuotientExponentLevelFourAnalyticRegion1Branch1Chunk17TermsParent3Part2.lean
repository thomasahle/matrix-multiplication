import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4750868644156663600152387541532672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    97613524329, 201, 1215841377987, 4358055559329, 304048674855, 9461199916761,
    164217, 9461202170151, 164217, 2255, 605236487797, 10519,
    605236631947, 10519, 63085, 1344023996075039, 7164535, 5936329,
    9791523140661617, 39916695, 2687880209921617, 159871481, 159871481, 114427859,
    5936329, 29535496641308881, 5829, 29535494726358831, 5829, 516727283,
    308461301889, 10251, 308461375359, 10251, 2255, 2035,
    184026199, 1839333323, 3678665747, 184026199, 64357841181, 230683913727,
    16094135865, 11712101005, 335, 11712103795, 335, 64357841181,
    230683913727, 16094135865, 605236487797, 10519, 605236631947, 10519,
    1045, 11712101005, 335, 11712103795, 335, 1045,
    71315445633, 255622715211, 17834042445, 308461301889
  ]
def negativeCoefficients : Array ℕ := #[
    450162925357470971487024316416, 485988179485080928231882752, 2803539341744068391950167834624, 10048991945243649496469584478208, 2804354045500356806500511907840, 10908020843418267487361864564736,
    12407885707478472448920256512, 10908023441400056753384771813376, 12407885707478472448920256512, 697888697147133129974381281280, 697790162153880819072470351872, 794793168532892768045891584,
    697790328347515708149461942272, 794793168532892768045891584, 1220241365286222103781425807360, 3026472983950275309430135324672, 4229194993668309196388433920, 219011883600680297670115328,
    11024274991918311752984856363008, 5890664455466573523541032960, 3026284077954881221672994603008, 5898216589383838361391726592, 5898216589383838361391726592, 4221642859751044358537740288,
    219011883600680297670115328, 8313503229250075789187860135936, 440426787658354591210143744, 8313502690239555063368317403136, 440426787658354591210143744, 2440175602023497814447088467968,
    711263336573705458640725475328, 774543661054347729369563136, 711263505983991345570820128768, 774543661054347729369563136, 697888697147133129974381281280, 39362624686652325928433090560,
    212167762238159038367924224, 8482427768906686627674324992, 8482425695953821344563462144, 212167762238159038367924224, 74199539087647017526578118656, 265960444902728920865074839552,
    74221101347291274564033576960, 27006266225583929194981621760, 25311884348181298345410560, 27006272658885924901187747840, 25311884348181298345410560, 74199539087647017526578118656,
    265960444902728920865074839552, 74221101347291274564033576960, 697790162153880819072470351872, 794793168532892768045891584, 697790328347515708149461942272, 794793168532892768045891584,
    40426479407913199602174525440, 27006266225583929194981621760, 25311884348181298345410560, 27006272658885924901187747840, 25311884348181298345410560, 40426479407913199602174525440,
    82221110880906154556478455808, 294712925432753669066704551936, 82245004195647088030415585280, 711263336573705458640725475328
  ]
def negativeScales : Array ℕ := #[
    36, 7, 40, 41, 38, 43,
    17, 43, 17, 11, 39, 13,
    39, 13, 15, 50, 22, 22,
    53, 25, 51, 27, 27, 26,
    22, 54, 12, 54, 12, 28,
    38, 13, 38, 13, 11, 10,
    27, 30, 31, 27, 35, 37,
    33, 33, 8, 33, 8, 35,
    37, 33, 39, 13, 39, 13,
    10, 33, 8, 33, 8, 10,
    36, 37, 34, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36506361995541851, 7651051691200812, 40145092161740178, 41986821746794262, 38145511345557022, 43105160303627571,
    17325243959324613, 43105160647236650, 17325243959324613, 11138911718142744, 39138708009466628, 13360709939349401,
    39138708353075234, 13360709939349401, 15945009399119717, 50255480319395424, 22772441641941018, 22501139619759487,
    53120454722011473, 25250488938381244, 51255390266634327, 27252337362773613, 27252337362773613, 26769863097819845,
    22501139619759487, 54713299389472576, 12509032686306867, 54713299295934652, 12509032686306867, 28944827828160694,
    38166298550721600, 13323477033150425, 38166298894345878, 13323477033150425, 11138911718142744, 10990813099588440,
    27455335930146138, 30776535802248583, 31776535449679803, 27455335930146138, 35905396886803484, 37747126448099542,
    33905816070656362, 33447280849444347, 8388017285345139, 33447281193116134, 8388017285345139, 35905396886803484,
    37747126448099542, 33905816070656362, 39138708009466628, 13360709939349401, 39138708353075234, 13360709939349401,
    10029287226968246, 33447280849444347, 8388017285345139, 33447281193116134, 8388017285345139, 10029287226968246,
    36053495520982825, 37895225090885785, 34053914704799669, 38166298550721600
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
noncomputable def negativeCeiling : ℝ := 2822009637 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 450162925357470971487024316416, coefficient := (-450162925357470971487024316416) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 2803539341744068391950167834624, coefficient := (-2803539341744068391950167834624) }, { argument := 10048991945243649496469584478208, coefficient := (-10048991945243649496469584478208) }, { argument := 2804354045500356806500511907840, coefficient := (-2804354045500356806500511907840) }, { argument := 10908020843418267487361864564736, coefficient := (-10908020843418267487361864564736) }, { argument := 12407885707478472448920256512, coefficient := (-12407885707478472448920256512) }, { argument := 10908023441400056753384771813376, coefficient := (-10908023441400056753384771813376) }, { argument := 12407885707478472448920256512, coefficient := (-12407885707478472448920256512) }, { argument := 697888697147133129974381281280, coefficient := (-697888697147133129974381281280) }, { argument := 697790162153880819072470351872, coefficient := (-697790162153880819072470351872) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 697790328347515708149461942272, coefficient := (-697790328347515708149461942272) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 1220241365286222103781425807360, coefficient := (-1220241365286222103781425807360) }, { argument := 3026472983950275309430135324672, coefficient := (-3026472983950275309430135324672) }, { argument := 4229194993668309196388433920, coefficient := (-4229194993668309196388433920) }, { argument := 219011883600680297670115328, coefficient := (-219011883600680297670115328) }, { argument := 11024274991918311752984856363008, coefficient := (-11024274991918311752984856363008) }, { argument := 5890664455466573523541032960, coefficient := (-5890664455466573523541032960) }, { argument := 3026284077954881221672994603008, coefficient := (-3026284077954881221672994603008) }, { argument := 5898216589383838361391726592, coefficient := (-5898216589383838361391726592) }, { argument := 5898216589383838361391726592, coefficient := (-5898216589383838361391726592) }, { argument := 4221642859751044358537740288, coefficient := (-4221642859751044358537740288) }, { argument := 219011883600680297670115328, coefficient := (-219011883600680297670115328) }, { argument := 8313503229250075789187860135936, coefficient := (-8313503229250075789187860135936) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 8313502690239555063368317403136, coefficient := (-8313502690239555063368317403136) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 2440175602023497814447088467968, coefficient := (-2440175602023497814447088467968) }, { argument := 711263336573705458640725475328, coefficient := (-711263336573705458640725475328) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 711263505983991345570820128768, coefficient := (-711263505983991345570820128768) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 697888697147133129974381281280, coefficient := (-697888697147133129974381281280) }, { argument := 39362624686652325928433090560, coefficient := (-39362624686652325928433090560) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 8482427768906686627674324992, coefficient := (-8482427768906686627674324992) }, { argument := 8482425695953821344563462144, coefficient := (-8482425695953821344563462144) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 74199539087647017526578118656, coefficient := (-74199539087647017526578118656) }, { argument := 265960444902728920865074839552, coefficient := (-265960444902728920865074839552) }, { argument := 74221101347291274564033576960, coefficient := (-74221101347291274564033576960) }, { argument := 27006266225583929194981621760, coefficient := (-27006266225583929194981621760) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 27006272658885924901187747840, coefficient := (-27006272658885924901187747840) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 74199539087647017526578118656, coefficient := (-74199539087647017526578118656) }, { argument := 265960444902728920865074839552, coefficient := (-265960444902728920865074839552) }, { argument := 74221101347291274564033576960, coefficient := (-74221101347291274564033576960) }, { argument := 697790162153880819072470351872, coefficient := (-697790162153880819072470351872) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 697790328347515708149461942272, coefficient := (-697790328347515708149461942272) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 40426479407913199602174525440, coefficient := (-40426479407913199602174525440) }, { argument := 27006266225583929194981621760, coefficient := (-27006266225583929194981621760) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 27006272658885924901187747840, coefficient := (-27006272658885924901187747840) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 40426479407913199602174525440, coefficient := (-40426479407913199602174525440) }, { argument := 82221110880906154556478455808, coefficient := (-82221110880906154556478455808) }, { argument := 294712925432753669066704551936, coefficient := (-294712925432753669066704551936) }, { argument := 82245004195647088030415585280, coefficient := (-82245004195647088030415585280) }, { argument := 711263336573705458640725475328, coefficient := (-711263336573705458640725475328) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 315161064759656631763948106445488128
def positiveArguments : Array ℕ := #[
    40839, 3, 87, 77, 5, 3,
    5, 153, 5, 3, 2451, 157,
    87, 153, 5, 157, 5, 153,
    5, 3, 81, 243, 513, 1323,
    1107, 30969, 945, 1107, 999, 513,
    513, 999, 30969, 999, 81, 1323,
    1389, 20835, 36577, 1389, 11575, 1389,
    36577, 72691, 11575, 1121849
  ]
def positiveCoefficients : Array ℕ := #[
    3235598928920041282982741387771904, 232113757366008801543585792, 3365649481807127622381993984, 5957586439060892572952035328, 193428131138340667952988160, 3713820117856140824697372672,
    193428131138340667952988160, 5918900812833224439361437696, 6189700196426901374495621120, 3713820117856140824697372672, 94818469884014595430554796032, 6073643317743896973723828224,
    3365649481807127622381993984, 5918900812833224439361437696, 193428131138340667952988160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696,
    6189700196426901374495621120, 232113757366008801543585792, 100273143182115802266829062144, 75204857386586851700121796608, 79382905019175010127906340864, 102362166998409881480721334272,
    1370399623488915964313330515968, 2396110317289308858334436130816, 73115833570292772486229524480, 1370399623488915964313330515968, 77293881202880930914014068736, 79382905019175010127906340864,
    79382905019175010127906340864, 77293881202880930914014068736, 2396110317289308858334436130816, 77293881202880930914014068736, 100273143182115802266829062144, 102362166998409881480721334272,
    107468669660462075114680221696, 1612030044906931126720203325440, 2830008301058834644686579171328, 107468669660462075114680221696, 1791144494341034585244670361600, 107468669660462075114680221696,
    2830008301058834644686579171328, 2812096856115424298834132467712, 1791144494341034585244670361600, 43399431097883268000478362861568
  ]
def positiveScales : Array ℕ := #[
    15, 1, 6, 6, 2, 1,
    2, 7, 2, 1, 11, 7,
    6, 7, 2, 7, 2, 7,
    2, 1, 6, 7, 9, 10,
    10, 14, 9, 10, 9, 9,
    9, 9, 14, 9, 6, 10,
    10, 14, 15, 10, 13, 10,
    15, 16, 13, 20
  ]
def negativeArguments : Array ℕ := #[
    10251, 308461375359, 10251, 2035, 308475293825, 335,
    308475367295, 335, 63085, 2035, 17746050137599, 201,
    17746049647105, 201, 13676045, 2695, 1, 27
  ]
def negativeCoefficients : Array ℕ := #[
    774543661054347729369563136, 711263505983991345570820128768, 774543661054347729369563136, 39362624686652325928433090560, 711295599781516424056825446400, 809980299141801547053137920,
    711295769191802310986920099840, 809980299141801547053137920, 1220241365286222103781425807360, 39362624686652325928433090560, 79921104786988995667352879104, 30374261217817558014492672,
    79921102578000400039888814080, 30374261217817558014492672, 64583296526216997076541112320, 52128881341782810013330309120, 158456325028528675187087900672, 8556641551540548460102746636288
  ]
def negativeScales : Array ℕ := #[
    13, 38, 13, 10, 38, 8,
    38, 8, 15, 10, 44, 7,
    44, 7, 23, 11, 0, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15317659919792980, 1584962500720924, 6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924,
    2321928094887362, 7257387842692651, 2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626,
    6442943495848725, 7257387842692651, 2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651,
    2321928094887362, 1584962500720924, 6339850002884624, 7924812503187618, 9002815015607054, 10369597346278676,
    10112439506781552, 14918537177804473, 9884170518905654, 10112439506781552, 9964340866974576, 9002815015607054,
    9002815015607054, 9964340866974576, 14918537177804473, 9964340866974576, 6339850002884624, 10369597346278676,
    10439830883981390, 14346721479589910, 15158649131437339, 10439830883981390, 13498724573034944, 10439830883981390,
    15158649131437339, 16149489132151863, 13498724573034944, 20097447072711582
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13323477033150425, 38166298894345878, 13323477033150425, 10990813099588440, 38166363990498794, 8388017285345139,
    38166364334107485, 8388017285345139, 15945009399119717, 10990813099588440, 44012563183165839, 7651051691200812,
    44012563143290303, 7651051691200812, 23705147739264751, 11396069557639874, 0, 4754887502413606
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 610879326689 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1825349419 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 711263505983991345570820128768, coefficient := (-711263505983991345570820128768) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 39362624686652325928433090560, coefficient := (-39362624686652325928433090560) }, { argument := 711295599781516424056825446400, coefficient := (-711295599781516424056825446400) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 711295769191802310986920099840, coefficient := (-711295769191802310986920099840) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 1220241365286222103781425807360, coefficient := (-1220241365286222103781425807360) }, { argument := 39362624686652325928433090560, coefficient := (-39362624686652325928433090560) }, { argument := 79921104786988995667352879104, coefficient := (-79921104786988995667352879104) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 79921102578000400039888814080, coefficient := (-79921102578000400039888814080) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 64583296526216997076541112320, coefficient := (-64583296526216997076541112320) }, { argument := 52128881341782810013330309120, coefficient := (-52128881341782810013330309120) }, { argument := 3235598928920041282982741387771904, coefficient := 3235598928920041282982741387771904 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 100273143182115802266829062144, coefficient := 100273143182115802266829062144 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 102362166998409881480721334272, coefficient := 102362166998409881480721334272 }, { argument := 1370399623488915964313330515968, coefficient := 1370399623488915964313330515968 }, { argument := 2396110317289308858334436130816, coefficient := 2396110317289308858334436130816 }, { argument := 73115833570292772486229524480, coefficient := 73115833570292772486229524480 }, { argument := 1370399623488915964313330515968, coefficient := 1370399623488915964313330515968 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 2396110317289308858334436130816, coefficient := 2396110317289308858334436130816 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 100273143182115802266829062144, coefficient := 100273143182115802266829062144 }, { argument := 102362166998409881480721334272, coefficient := 102362166998409881480721334272 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 1612030044906931126720203325440, coefficient := 1612030044906931126720203325440 }, { argument := 2830008301058834644686579171328, coefficient := 2830008301058834644686579171328 }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 1791144494341034585244670361600, coefficient := 1791144494341034585244670361600 }, { argument := 107468669660462075114680221696, coefficient := 107468669660462075114680221696 }, { argument := 2830008301058834644686579171328, coefficient := 2830008301058834644686579171328 }, { argument := 2812096856115424298834132467712, coefficient := 2812096856115424298834132467712 }, { argument := 1791144494341034585244670361600, coefficient := 1791144494341034585244670361600 }, { argument := 43399431097883268000478362861568, coefficient := 43399431097883268000478362861568 }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
