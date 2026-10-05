import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

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
def constantNumerator : ℤ := (-4081575868532797376193178932084736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1346836755, 20460812337, 3203025416787, 800756647887, 81844424109, 86272285,
    55580291415, 591119772287, 27790229467, 86272285, 37007659017, 5793341461467,
    1448335896567, 148032760869, 11701152565, 41941550855, 2926138225, 28667757823191,
    892802245933865, 2327710959, 188733321, 40451841801, 73165617441, 892802252282665,
    40451841801, 1195311033, 1195311033, 2327710959, 2327710959, 73165617441,
    2327710959, 28667751474391, 188733321, 490999300697, 10475480774141, 1698910213,
    196244696816243, 66191307, 110318845, 3375756657, 110318845, 66191307,
    54078297819, 3464011733, 10475483744669, 3375756657, 110318845, 3464011733,
    110318845, 3375756657, 110318845, 490999300697, 448419250960057, 948794665,
    4211436802416645, 10707825505, 948794665, 8422871658800445, 948794665, 948794665,
    39334315969, 243975771, 10707825505, 39334315969
  ]
def negativeCoefficients : Array ℕ := #[
    12422376464275226655499223040, 94358842180209507764847771648, 3692836882816041175876330586112, 3692838237223260849320490958848, 94360196587429181209008144384, 795721381024565722118881280,
    256318852818675279721566044160, 2726058789071939223656698216448, 256319625363705400659160334336, 795721381024565722118881280, 170667703663427150125222330368, 6679267954455763433194669473792,
    6679270404184529343327730925568, 170670153392193060258283782144, 107924083366992534478279147520, 386842527338329513800855715840, 107955445921747473062376243200, 8069256465629413072013623296,
    251301491381456021348616765440, 5367336042280253384942419968, 6963030541336544931817193472, 93275596626654133149134487552, 168708427491133369910487416832, 251301493168484353489229578240,
    93275596626654133149134487552, 5512399178558098071021944832, 5512399178558098071021944832, 5367336042280253384942419968, 5367336042280253384942419968, 168708427491133369910487416832,
    5367336042280253384942419968, 8069254678601080931400810496, 6963030541336544931817193472, 17690114141265466535440285696, 1509675881950342482249700605952, 250714895227379056288584433664,
    14140920695281087000527868264448, 156289804817067463660416270336, 8140094000888930398980014080, 249086876427201270208788430848, 260483008028445772767360450560, 156289804817067463660416270336,
    3990274079235753681580002902016, 255598951627912414527972442112, 1509676310048543886845692346368, 249086876427201270208788430848, 8140094000888930398980014080, 255598951627912414527972442112,
    8140094000888930398980014080, 249086876427201270208788430848, 260483008028445772767360450560, 17690114141265466535440285696, 252437596441183704487804534784, 17502172363755989332802928640,
    9483312607028997805069786152960, 197524516676674736755918766080, 17502172363755989332802928640, 9483310415990798906883236167680, 17502172363755989332802928640, 17502172363755989332802928640,
    725590059994569729197058555904, 18002234431291874742311583744, 197524516676674736755918766080, 725590059994569729197058555904
  ]
def negativeScales : Array ℕ := #[
    30, 34, 41, 39, 36, 26,
    35, 39, 34, 26, 35, 42,
    40, 37, 33, 35, 31, 44,
    49, 31, 27, 35, 36, 49,
    35, 30, 30, 31, 31, 36,
    31, 44, 27, 38, 43, 30,
    47, 25, 26, 31, 26, 25,
    35, 31, 43, 31, 26, 31,
    26, 31, 26, 38, 48, 29,
    51, 33, 29, 52, 29, 29,
    35, 27, 33, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30326927851761846, 34252144373101372, 41542572384944045, 39542572914075518, 36252165081097682, 26362393831786635,
    35693854347740140, 39104659521672284, 34693858696016491, 26362393831786635, 35107104827246643, 42397532839088262,
    40397533368219735, 37107125535242953, 33445931591324576, 35287661157219222, 31446350775141421, 44704494305831138,
    49665333984870572, 31116264778252054, 27491773913344466, 35235486339951052, 36090446794096323, 49665333995129711,
    35235486339951052, 30154738926066690, 30154738926066690, 31116264778252054, 31116264778252054, 36090446794096323,
    31116264778252054, 44704493986329928, 27491773913344466, 38836930014898928, 43252081691737386, 30661962462462724,
    47479646996540685, 25980138439648361, 26717104016734072, 31652563764454411, 26717104016734072, 25980138439648361,
    35654330690629639, 31689796670687481, 43252082100841798, 31652563764454411, 26717104016734072, 31689796670687481,
    26717104016734072, 31652563764454411, 26717104016734072, 38836930014898928, 48671841543865542, 29821520657837083,
    51903233944860351, 33317946482960997, 29821520657837083, 52903233611537946, 29821520657837083, 29821520657837083,
    35195069443963276, 27862162643519687, 33317946482960997, 35195069443963276
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
noncomputable def negativeCeiling : ℝ := 7587821209 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12422376464275226655499223040, coefficient := (-12422376464275226655499223040) }, { argument := 94358842180209507764847771648, coefficient := (-94358842180209507764847771648) }, { argument := 3692836882816041175876330586112, coefficient := (-3692836882816041175876330586112) }, { argument := 3692838237223260849320490958848, coefficient := (-3692838237223260849320490958848) }, { argument := 94360196587429181209008144384, coefficient := (-94360196587429181209008144384) }, { argument := 795721381024565722118881280, coefficient := (-795721381024565722118881280) }, { argument := 256318852818675279721566044160, coefficient := (-256318852818675279721566044160) }, { argument := 2726058789071939223656698216448, coefficient := (-2726058789071939223656698216448) }, { argument := 256319625363705400659160334336, coefficient := (-256319625363705400659160334336) }, { argument := 795721381024565722118881280, coefficient := (-795721381024565722118881280) }, { argument := 170667703663427150125222330368, coefficient := (-170667703663427150125222330368) }, { argument := 6679267954455763433194669473792, coefficient := (-6679267954455763433194669473792) }, { argument := 6679270404184529343327730925568, coefficient := (-6679270404184529343327730925568) }, { argument := 170670153392193060258283782144, coefficient := (-170670153392193060258283782144) }, { argument := 107924083366992534478279147520, coefficient := (-107924083366992534478279147520) }, { argument := 386842527338329513800855715840, coefficient := (-386842527338329513800855715840) }, { argument := 107955445921747473062376243200, coefficient := (-107955445921747473062376243200) }, { argument := 8069256465629413072013623296, coefficient := (-8069256465629413072013623296) }, { argument := 251301491381456021348616765440, coefficient := (-251301491381456021348616765440) }, { argument := 5367336042280253384942419968, coefficient := (-5367336042280253384942419968) }, { argument := 6963030541336544931817193472, coefficient := (-6963030541336544931817193472) }, { argument := 93275596626654133149134487552, coefficient := (-93275596626654133149134487552) }, { argument := 168708427491133369910487416832, coefficient := (-168708427491133369910487416832) }, { argument := 251301493168484353489229578240, coefficient := (-251301493168484353489229578240) }, { argument := 93275596626654133149134487552, coefficient := (-93275596626654133149134487552) }, { argument := 5512399178558098071021944832, coefficient := (-5512399178558098071021944832) }, { argument := 5512399178558098071021944832, coefficient := (-5512399178558098071021944832) }, { argument := 5367336042280253384942419968, coefficient := (-5367336042280253384942419968) }, { argument := 5367336042280253384942419968, coefficient := (-5367336042280253384942419968) }, { argument := 168708427491133369910487416832, coefficient := (-168708427491133369910487416832) }, { argument := 5367336042280253384942419968, coefficient := (-5367336042280253384942419968) }, { argument := 8069254678601080931400810496, coefficient := (-8069254678601080931400810496) }, { argument := 6963030541336544931817193472, coefficient := (-6963030541336544931817193472) }, { argument := 17690114141265466535440285696, coefficient := (-17690114141265466535440285696) }, { argument := 1509675881950342482249700605952, coefficient := (-1509675881950342482249700605952) }, { argument := 250714895227379056288584433664, coefficient := (-250714895227379056288584433664) }, { argument := 14140920695281087000527868264448, coefficient := (-14140920695281087000527868264448) }, { argument := 156289804817067463660416270336, coefficient := (-156289804817067463660416270336) }, { argument := 8140094000888930398980014080, coefficient := (-8140094000888930398980014080) }, { argument := 249086876427201270208788430848, coefficient := (-249086876427201270208788430848) }, { argument := 260483008028445772767360450560, coefficient := (-260483008028445772767360450560) }, { argument := 156289804817067463660416270336, coefficient := (-156289804817067463660416270336) }, { argument := 3990274079235753681580002902016, coefficient := (-3990274079235753681580002902016) }, { argument := 255598951627912414527972442112, coefficient := (-255598951627912414527972442112) }, { argument := 1509676310048543886845692346368, coefficient := (-1509676310048543886845692346368) }, { argument := 249086876427201270208788430848, coefficient := (-249086876427201270208788430848) }, { argument := 8140094000888930398980014080, coefficient := (-8140094000888930398980014080) }, { argument := 255598951627912414527972442112, coefficient := (-255598951627912414527972442112) }, { argument := 8140094000888930398980014080, coefficient := (-8140094000888930398980014080) }, { argument := 249086876427201270208788430848, coefficient := (-249086876427201270208788430848) }, { argument := 260483008028445772767360450560, coefficient := (-260483008028445772767360450560) }, { argument := 17690114141265466535440285696, coefficient := (-17690114141265466535440285696) }, { argument := 252437596441183704487804534784, coefficient := (-252437596441183704487804534784) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 9483312607028997805069786152960, coefficient := (-9483312607028997805069786152960) }, { argument := 197524516676674736755918766080, coefficient := (-197524516676674736755918766080) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 9483310415990798906883236167680, coefficient := (-9483310415990798906883236167680) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 725590059994569729197058555904, coefficient := (-725590059994569729197058555904) }, { argument := 18002234431291874742311583744, coefficient := (-18002234431291874742311583744) }, { argument := 197524516676674736755918766080, coefficient := (-197524516676674736755918766080) }, { argument := 725590059994569729197058555904, coefficient := (-725590059994569729197058555904) }] }

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
def constantNumerator : ℤ := (-1064054725695715534438105928957952)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    448419381919417, 948794665, 243975771, 948794665, 84074265, 54164233035,
    576059395923, 27082198143, 84074265, 20460812337, 3203025416787, 800756647887,
    81844424109, 20801194294483, 150513260305115, 41607554263935, 604596321, 94646163171,
    23661549471, 2418419997, 77227606929, 276814235643, 19312512285, 2155871485,
    2155873027, 41612375, 7298419625, 1824605125, 10402875, 2747525,
    1770072975, 18825470455, 885039155, 2747525, 10700325, 1876736475,
    469184175, 2675025, 86272285, 55580291415, 591119772287, 27790229467,
    86272285, 604596321, 94646163171, 23661549471, 2418419997, 2747525,
    1770072975, 18825470455, 885039155, 2747525, 1177371783, 184310949333,
    46077754233, 4709554731, 3818270837, 13686190279, 954845105, 41612375,
    7298419625, 1824605125, 10402875, 84074265
  ]
def negativeCoefficients : Array ℕ := #[
    252437670164749316572634415104, 17502172363755989332802928640, 18002234431291874742311583744, 17502172363755989332802928640, 775448224820118187797381120, 249788436186352342658596208640,
    2656605061961826122417037115392, 249789189048706536948098924544, 775448224820118187797381120, 94358842180209507764847771648, 3692836882816041175876330586112, 3692838237223260849320490958848,
    94360196587429181209008144384, 187360501746989852478339547136, 677851463024434381082108887040, 187383765878855357976815861760, 5576416800696673864796602368, 218239193696748934188647841792,
    218239273739477313023605997568, 5576496843425052699754758144, 89037368777768840944580296704, 319145085054121848885705965568, 89063242885441665276460400640, 9942202384900790125267517440,
    9942209496120630540299665408, 95951603990528687865856000, 16829009870614279758020608000, 16829011888226912820002816000, 95949586377895625883648000, 25341445255559417901875200,
    8163020790403671328712294400, 86817158887641376549576376320, 8163045393748579638826762240, 25341445255559417901875200, 98693078390258078947737600, 17309838724060402036821196800,
    17309840799319110329145753600, 98691003131549786623180800, 795721381024565722118881280, 256318852818675279721566044160, 2726058789071939223656698216448, 256319625363705400659160334336,
    795721381024565722118881280, 5576416800696673864796602368, 218239193696748934188647841792, 218239273739477313023605997568, 5576496843425052699754758144, 25341445255559417901875200,
    8163020790403671328712294400, 86817158887641376549576376320, 8163045393748579638826762240, 25341445255559417901875200, 5429668990152024552565112832, 212496057020518699078420267008,
    212496134956859488996668997632, 5429746926492814470813843456, 4402166558390484958982438912, 15779103088800282799771746304, 4403445820492331138070609920, 95951603990528687865856000,
    16829009870614279758020608000, 16829011888226912820002816000, 95949586377895625883648000, 775448224820118187797381120
  ]
def negativeScales : Array ℕ := #[
    48, 29, 27, 29, 26, 35,
    39, 34, 26, 34, 41, 39,
    36, 44, 47, 45, 29, 36,
    34, 31, 36, 38, 34, 31,
    31, 25, 32, 30, 23, 21,
    30, 34, 29, 21, 23, 30,
    28, 21, 26, 35, 39, 34,
    26, 29, 36, 34, 31, 21,
    30, 34, 29, 21, 30, 37,
    35, 32, 31, 33, 29, 25,
    32, 30, 23, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    48671841965199798, 29821520657837083, 27862162643519687, 29821520657837083, 26325160925587658, 35656621441503757,
    39067426615473308, 34656625789780103, 26325160925587658, 34252144373101372, 41542572384944045, 39542572914075518,
    36252165081097682, 44241731596193626, 47096883923273153, 45241910721269661, 29171396959217010, 36461824971058695,
    34461825500190168, 31171417667213320, 36168397615795627, 38010127181690313, 34168816799612471, 31005624033245834,
    31005625065141739, 25310509295851609, 32764936955822540, 30764937128785751, 23310478959408832, 21389701177782373,
    30721161693791430, 34131966867668019, 29721166042067786, 21389701177782373, 23351151280348956, 30805578940732813,
    28805579113696026, 21351120943906178, 26362393831786635, 35693854347740140, 39104659521672284, 34693858696016491,
    26362393831786635, 29171396959217010, 36461824971058695, 34461825500190168, 31171417667213320, 21389701177782373,
    30721161693791430, 34131966867668019, 29721166042067786, 21389701177782373, 30132922811402374, 37423350823244004,
    35423351352375477, 32132943519398684, 31830272294563334, 33672001859312080, 29830691478389925, 25310509295851609,
    32764936955822540, 30764937128785751, 23310478959408832, 26325160925587658
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
noncomputable def negativeCeiling : ℝ := 8330459901 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 252437670164749316572634415104, coefficient := (-252437670164749316572634415104) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 18002234431291874742311583744, coefficient := (-18002234431291874742311583744) }, { argument := 17502172363755989332802928640, coefficient := (-17502172363755989332802928640) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }, { argument := 249788436186352342658596208640, coefficient := (-249788436186352342658596208640) }, { argument := 2656605061961826122417037115392, coefficient := (-2656605061961826122417037115392) }, { argument := 249789189048706536948098924544, coefficient := (-249789189048706536948098924544) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }, { argument := 94358842180209507764847771648, coefficient := (-94358842180209507764847771648) }, { argument := 3692836882816041175876330586112, coefficient := (-3692836882816041175876330586112) }, { argument := 3692838237223260849320490958848, coefficient := (-3692838237223260849320490958848) }, { argument := 94360196587429181209008144384, coefficient := (-94360196587429181209008144384) }, { argument := 187360501746989852478339547136, coefficient := (-187360501746989852478339547136) }, { argument := 677851463024434381082108887040, coefficient := (-677851463024434381082108887040) }, { argument := 187383765878855357976815861760, coefficient := (-187383765878855357976815861760) }, { argument := 5576416800696673864796602368, coefficient := (-5576416800696673864796602368) }, { argument := 218239193696748934188647841792, coefficient := (-218239193696748934188647841792) }, { argument := 218239273739477313023605997568, coefficient := (-218239273739477313023605997568) }, { argument := 5576496843425052699754758144, coefficient := (-5576496843425052699754758144) }, { argument := 89037368777768840944580296704, coefficient := (-89037368777768840944580296704) }, { argument := 319145085054121848885705965568, coefficient := (-319145085054121848885705965568) }, { argument := 89063242885441665276460400640, coefficient := (-89063242885441665276460400640) }, { argument := 9942202384900790125267517440, coefficient := (-9942202384900790125267517440) }, { argument := 9942209496120630540299665408, coefficient := (-9942209496120630540299665408) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 8163020790403671328712294400, coefficient := (-8163020790403671328712294400) }, { argument := 86817158887641376549576376320, coefficient := (-86817158887641376549576376320) }, { argument := 8163045393748579638826762240, coefficient := (-8163045393748579638826762240) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 98693078390258078947737600, coefficient := (-98693078390258078947737600) }, { argument := 17309838724060402036821196800, coefficient := (-17309838724060402036821196800) }, { argument := 17309840799319110329145753600, coefficient := (-17309840799319110329145753600) }, { argument := 98691003131549786623180800, coefficient := (-98691003131549786623180800) }, { argument := 795721381024565722118881280, coefficient := (-795721381024565722118881280) }, { argument := 256318852818675279721566044160, coefficient := (-256318852818675279721566044160) }, { argument := 2726058789071939223656698216448, coefficient := (-2726058789071939223656698216448) }, { argument := 256319625363705400659160334336, coefficient := (-256319625363705400659160334336) }, { argument := 795721381024565722118881280, coefficient := (-795721381024565722118881280) }, { argument := 5576416800696673864796602368, coefficient := (-5576416800696673864796602368) }, { argument := 218239193696748934188647841792, coefficient := (-218239193696748934188647841792) }, { argument := 218239273739477313023605997568, coefficient := (-218239273739477313023605997568) }, { argument := 5576496843425052699754758144, coefficient := (-5576496843425052699754758144) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 8163020790403671328712294400, coefficient := (-8163020790403671328712294400) }, { argument := 86817158887641376549576376320, coefficient := (-86817158887641376549576376320) }, { argument := 8163045393748579638826762240, coefficient := (-8163045393748579638826762240) }, { argument := 25341445255559417901875200, coefficient := (-25341445255559417901875200) }, { argument := 5429668990152024552565112832, coefficient := (-5429668990152024552565112832) }, { argument := 212496057020518699078420267008, coefficient := (-212496057020518699078420267008) }, { argument := 212496134956859488996668997632, coefficient := (-212496134956859488996668997632) }, { argument := 5429746926492814470813843456, coefficient := (-5429746926492814470813843456) }, { argument := 4402166558390484958982438912, coefficient := (-4402166558390484958982438912) }, { argument := 15779103088800282799771746304, coefficient := (-15779103088800282799771746304) }, { argument := 4403445820492331138070609920, coefficient := (-4403445820492331138070609920) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 775448224820118187797381120, coefficient := (-775448224820118187797381120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
