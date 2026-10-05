import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-998531868631242720475006149591040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    153615, 173565, 14331210801051, 48195, 37485, 5355,
    50337, 594405, 41769, 37485, 594405, 5355,
    41769, 41769, 41769, 41769, 41769, 48195,
    50337, 973254985, 129530607965, 4840155, 4963853289335, 4966695,
    158175, 4840155, 2752245, 4966695, 77537385, 94905,
    129530607965, 4840155, 158175, 94905, 158175, 2435895,
    2752245, 3892664445, 11912779517137, 433662666796719, 3469259840898855, 95343760301273,
    32796145, 3372978725, 43605, 119765639375, 44745, 1425,
    43605, 24795, 44745, 698535, 855, 3372978725,
    43605, 1425, 855, 1425, 21945, 24795,
    131176005, 4523057091, 83667175329, 83662196763
  ]
def negativeCoefficients : Array ℕ := #[
    1450852654532041099003822080, 819637538599269971515146240, 32271017811690655542461595648, 1820755621135220408592629760, 1416143260882949206683156480, 1618449441009084807637893120,
    1901678093185674648974524416, 22455985994001051705975767040, 50495622559483445998302265344, 1416143260882949206683156480, 22455985994001051705975767040, 1618449441009084807637893120,
    1577988204983857687446945792, 1577988204983857687446945792, 1577988204983857687446945792, 50495622559483445998302265344, 1577988204983857687446945792, 1820755621135220408592629760,
    1901678093185674648974524416, 4488346406689257138096701440, 597354493710589748412007055360, 22856985743893927629296762880, 5722933202987754717780597800960, 23454553998636252534637854720,
    746960318427906131676364800, 22856985743893927629296762880, 12997109540645566691168747520, 23454553998636252534637854720, 366159948093359585747754024960, 14341638113815797728186204160,
    597354493710589748412007055360, 22856985743893927629296762880, 746960318427906131676364800, 14341638113815797728186204160, 746960318427906131676364800, 23006377807579508855632035840,
    12997109540645566691168747520, 4487936548858976927030968320, 107300778788650140935760379904, 3906086049180398513242660405248, 3906039331680877404185186795520, 107347530841228743060437860352,
    151245523354817285670830080, 15555118826535537357514342400, 1647350323884247036345712640, 138080381148426036083425280000, 1690418306208018200694620160, 53834977904713955436134400,
    1647350323884247036345712640, 936728615542022824588738560, 1690418306208018200694620160, 26389906168890780954793082880, 1033631575770507944373780480, 15555118826535537357514342400,
    1647350323884247036345712640, 53834977904713955436134400, 1033631575770507944373780480, 53834977904713955436134400, 1658117319465189827432939520, 936728615542022824588738560,
    151235637052915281958010880, 20858919147113553527794827264, 771693485332124377238923640832, 771647566165696341305148309504
  ]
def negativeScales : Array ℕ := #[
    17, 17, 43, 15, 15, 12,
    15, 19, 15, 15, 19, 12,
    15, 15, 15, 15, 15, 15,
    15, 29, 36, 22, 42, 22,
    17, 22, 21, 22, 26, 16,
    36, 22, 17, 16, 17, 21,
    21, 31, 43, 48, 51, 46,
    24, 31, 15, 36, 15, 10,
    15, 14, 15, 19, 9, 31,
    15, 10, 9, 10, 14, 14,
    26, 32, 36, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17228959571804610, 17405116526958445, 43704225737345359, 15556595861081553, 15194025781695223, 12386670859637623,
    15619331616437464, 19181086725987725, 15350144983612506, 15194025781695223, 19181086725987725, 12386670859637623,
    15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506, 15556595861081553,
    15619331616437464, 29858242590182122, 36914502095136417, 22206621818094862, 42174597614737754, 22243854724293838,
    17271162070289573, 22206621818094862, 21392177471250944, 22243854724293838, 26208388744269050, 16534196476124184,
    36914502095136417, 22206621818094862, 17271162070289573, 16534196476124184, 17271162070289573, 21216020516097112,
    21392177471250944, 31858110843024607, 43437575298941170, 48623566578078108, 51623549323079855, 46438203759100856,
    24967022922294076, 31651376072621171, 15412205951744767, 36801423104358473, 15449438857943777, 10476746203939589,
    15412205951744767, 14597761604906147, 15449438857943777, 19413972877918956, 9739780609952834, 31651376072621171,
    15412205951744767, 10476746203939589, 9739780609952834, 10476746203939589, 14421604649747022, 14597761604906147,
    26966928616109969, 32074651060077797, 36283942678240520, 36283856828967421
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
noncomputable def negativeCeiling : ℝ := 9247971363 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1450852654532041099003822080, coefficient := (-1450852654532041099003822080) }, { argument := 819637538599269971515146240, coefficient := (-819637538599269971515146240) }, { argument := 32271017811690655542461595648, coefficient := (-32271017811690655542461595648) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }, { argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 4488346406689257138096701440, coefficient := (-4488346406689257138096701440) }, { argument := 597354493710589748412007055360, coefficient := (-597354493710589748412007055360) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 5722933202987754717780597800960, coefficient := (-5722933202987754717780597800960) }, { argument := 23454553998636252534637854720, coefficient := (-23454553998636252534637854720) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 12997109540645566691168747520, coefficient := (-12997109540645566691168747520) }, { argument := 23454553998636252534637854720, coefficient := (-23454553998636252534637854720) }, { argument := 366159948093359585747754024960, coefficient := (-366159948093359585747754024960) }, { argument := 14341638113815797728186204160, coefficient := (-14341638113815797728186204160) }, { argument := 597354493710589748412007055360, coefficient := (-597354493710589748412007055360) }, { argument := 22856985743893927629296762880, coefficient := (-22856985743893927629296762880) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 14341638113815797728186204160, coefficient := (-14341638113815797728186204160) }, { argument := 746960318427906131676364800, coefficient := (-746960318427906131676364800) }, { argument := 23006377807579508855632035840, coefficient := (-23006377807579508855632035840) }, { argument := 12997109540645566691168747520, coefficient := (-12997109540645566691168747520) }, { argument := 4487936548858976927030968320, coefficient := (-4487936548858976927030968320) }, { argument := 107300778788650140935760379904, coefficient := (-107300778788650140935760379904) }, { argument := 3906086049180398513242660405248, coefficient := (-3906086049180398513242660405248) }, { argument := 3906039331680877404185186795520, coefficient := (-3906039331680877404185186795520) }, { argument := 107347530841228743060437860352, coefficient := (-107347530841228743060437860352) }, { argument := 151245523354817285670830080, coefficient := (-151245523354817285670830080) }, { argument := 15555118826535537357514342400, coefficient := (-15555118826535537357514342400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 138080381148426036083425280000, coefficient := (-138080381148426036083425280000) }, { argument := 1690418306208018200694620160, coefficient := (-1690418306208018200694620160) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 936728615542022824588738560, coefficient := (-936728615542022824588738560) }, { argument := 1690418306208018200694620160, coefficient := (-1690418306208018200694620160) }, { argument := 26389906168890780954793082880, coefficient := (-26389906168890780954793082880) }, { argument := 1033631575770507944373780480, coefficient := (-1033631575770507944373780480) }, { argument := 15555118826535537357514342400, coefficient := (-15555118826535537357514342400) }, { argument := 1647350323884247036345712640, coefficient := (-1647350323884247036345712640) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }, { argument := 1033631575770507944373780480, coefficient := (-1033631575770507944373780480) }, { argument := 53834977904713955436134400, coefficient := (-53834977904713955436134400) }, { argument := 1658117319465189827432939520, coefficient := (-1658117319465189827432939520) }, { argument := 936728615542022824588738560, coefficient := (-936728615542022824588738560) }, { argument := 151235637052915281958010880, coefficient := (-151235637052915281958010880) }, { argument := 20858919147113553527794827264, coefficient := (-20858919147113553527794827264) }, { argument := 771693485332124377238923640832, coefficient := (-771693485332124377238923640832) }, { argument := 771647566165696341305148309504, coefficient := (-771647566165696341305148309504) }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-50057324322457589659668867710976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4533022917, 4079274101, 6971668363, 4079274101, 1575, 1225,
    175, 1645, 19425, 1365, 1225, 19425,
    175, 1365, 1365, 1365, 1365, 1365,
    1575, 1645, 945, 735, 105, 987,
    11655, 819, 735, 11655, 105, 819,
    819, 819, 819, 819, 945, 987,
    32445937, 3363639845, 340119, 119764472015, 349011, 11115,
    340119, 193401, 349011, 5448573, 6669, 3363639845,
    340119, 11115, 6669, 11115, 171171, 193401,
    129775173, 1575, 1225, 175, 1645, 19425,
    1365, 1225, 19425, 175
  ]
def negativeCoefficients : Array ℕ := #[
    20904878407539833669280595968, 75249325347658608903471497216, 257209164118077242104365449216, 75249325347658608903471497216, 59501817684157529692569600, 46279191532122523094220800,
    52890504608140026393395200, 62146342914564531012239360, 733855751437942866208358400, 1650183743773968823473930240, 46279191532122523094220800, 733855751437942866208358400,
    52890504608140026393395200, 51568241992936525733560320, 51568241992936525733560320, 51568241992936525733560320, 1650183743773968823473930240, 51568241992936525733560320,
    59501817684157529692569600, 62146342914564531012239360, 1142434899535824570097336320, 888560477416752443409039360, 1015497688476288506753187840, 1193209783959638995434995712,
    14090030427608503031200481280, 31683527880460201410699460608, 888560477416752443409039360, 14090030427608503031200481280, 1015497688476288506753187840, 990110246264381294084358144,
    990110246264381294084358144, 990110246264381294084358144, 31683527880460201410699460608, 990110246264381294084358144, 1142434899535824570097336320, 1193209783959638995434995712,
    149630474017675867007746048, 15512050844211766193165434880, 1606166565787140860437069824, 138079035273978418234539376640, 1648157848552817745677254656, 52489103457096106550231040,
    1606166565787140860437069824, 913310400153472253974020096, 1648157848552817745677254656, 25730158514668511430923255808, 1007790786376245245764435968, 15512050844211766193165434880,
    1606166565787140860437069824, 52489103457096106550231040, 1007790786376245245764435968, 52489103457096106550231040, 1616664386478560081747116032, 913310400153472253974020096,
    149620587715773863294926848, 59501817684157529692569600, 46279191532122523094220800, 52890504608140026393395200, 62146342914564531012239360, 733855751437942866208358400,
    1650183743773968823473930240, 46279191532122523094220800, 733855751437942866208358400, 52890504608140026393395200
  ]
def negativeScales : Array ℕ := #[
    32, 31, 32, 31, 10, 10,
    7, 10, 14, 10, 10, 14,
    7, 10, 10, 10, 10, 10,
    10, 10, 9, 9, 6, 9,
    13, 9, 9, 13, 6, 9,
    9, 9, 9, 9, 9, 9,
    24, 31, 18, 36, 18, 13,
    18, 17, 18, 22, 12, 31,
    18, 13, 12, 13, 17, 17,
    26, 10, 10, 7, 10, 14,
    10, 10, 14, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32077826308869696, 31925665311078071, 32698856797238788, 31925665311078071, 10621136113284685, 10258566033889934,
    7451211111832378, 10683871868671904, 14245626978182435, 10414685235807227, 10258566033889934, 14245626978182435,
    7451211111832378, 10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227,
    10621136113284685, 10683871868671904, 9884170522387776, 9521600439724276, 6714245517766967, 9946906284348933,
    13508661384016590, 9677719641683481, 9521600439724276, 13508661384016590, 6714245517766967, 9677719641683481,
    9677719641683481, 9677719641683481, 9677719641683481, 9677719641683481, 9884170522387776, 9946906284348933,
    24951534504845379, 31647376094186436, 18375680075719645, 36801409042289233, 18412912981918629, 13440220327914385,
    18375680075719645, 17561235728877581, 18412912981918629, 22377447001893833, 12703254733826280, 31647376094186436,
    18375680075719645, 13440220327914385, 12703254733826280, 13440220327914385, 17385078773721895, 17561235728877581,
    26951439180730442, 10621136113284685, 10258566033889934, 7451211111832378, 10683871868671904, 14245626978182435,
    10414685235807227, 10258566033889934, 14245626978182435, 7451211111832378
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
noncomputable def negativeCeiling : ℝ := 132298351 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20904878407539833669280595968, coefficient := (-20904878407539833669280595968) }, { argument := 75249325347658608903471497216, coefficient := (-75249325347658608903471497216) }, { argument := 257209164118077242104365449216, coefficient := (-257209164118077242104365449216) }, { argument := 75249325347658608903471497216, coefficient := (-75249325347658608903471497216) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 888560477416752443409039360, coefficient := (-888560477416752443409039360) }, { argument := 1015497688476288506753187840, coefficient := (-1015497688476288506753187840) }, { argument := 1193209783959638995434995712, coefficient := (-1193209783959638995434995712) }, { argument := 14090030427608503031200481280, coefficient := (-14090030427608503031200481280) }, { argument := 31683527880460201410699460608, coefficient := (-31683527880460201410699460608) }, { argument := 888560477416752443409039360, coefficient := (-888560477416752443409039360) }, { argument := 14090030427608503031200481280, coefficient := (-14090030427608503031200481280) }, { argument := 1015497688476288506753187840, coefficient := (-1015497688476288506753187840) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 31683527880460201410699460608, coefficient := (-31683527880460201410699460608) }, { argument := 990110246264381294084358144, coefficient := (-990110246264381294084358144) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1193209783959638995434995712, coefficient := (-1193209783959638995434995712) }, { argument := 149630474017675867007746048, coefficient := (-149630474017675867007746048) }, { argument := 15512050844211766193165434880, coefficient := (-15512050844211766193165434880) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 138079035273978418234539376640, coefficient := (-138079035273978418234539376640) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 25730158514668511430923255808, coefficient := (-25730158514668511430923255808) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 15512050844211766193165434880, coefficient := (-15512050844211766193165434880) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1616664386478560081747116032, coefficient := (-1616664386478560081747116032) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 149620587715773863294926848, coefficient := (-149620587715773863294926848) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 46279191532122523094220800, coefficient := (-46279191532122523094220800) }, { argument := 733855751437942866208358400, coefficient := (-733855751437942866208358400) }, { argument := 52890504608140026393395200, coefficient := (-52890504608140026393395200) }] }

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

end TermShard7


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
