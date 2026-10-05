import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2

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
def constantNumerator : ℤ := 1477725810068214316624590667776
def positiveArguments : Array ℕ := #[
    7, 262033, 262255, 9055737, 64436459, 18115363,
    1282515, 12262281, 6131137, 1282561, 46973, 1348989,
    13985335, 674463, 46993
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 79194614822770031633945853952, 79261710205758643553142046720, 171058035545930049354159095808, 608585148512808192313737084928, 171094766112433809454631223296,
    12113011699555126062486650880, 463255878383434207845163204608, 463255613930911167145031237632, 12113446157271550069846310912, 443647441599671689245884416, 12740840878719679654357106688,
    132087754511407499289370296320, 12740245860542838079060180992, 443836336258986475054432256
  ]
def positiveScales : Array ℕ := #[
    2, 17, 18, 23, 25, 24,
    20, 23, 22, 20, 15, 20,
    23, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    12308476109, 353479634637, 3664619286055, 176731563279, 12313716769, 968396875623,
    74028220093899, 74028179172575, 242107833809, 968396875623, 1721046126937, 968768665063,
    12308476109, 12318904115, 12318904115, 353779110195, 3667724030425, 176881294065,
    12324149215, 1721046126937, 526763731713341, 526763424872661, 6884432658323, 74028220093899,
    526763731713341, 148087576057645, 353479634637, 353779110195, 968768665063, 148087576057645,
    148087494978925, 1937606136293, 74028179172575, 526763424872661, 148087494978925, 3664619286055,
    3667724030425, 242107833809, 6884432658323, 1937606136293, 176731563279, 176881294065,
    12313716769, 12324149215, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    110864896835982105014960128, 3183861501668504542226939904, 33007956102264062176982466560, 3183712810111638536806465536, 110912100504828455942094848, 1090317952050623840362954752,
    41674183053723075100947775488, 41674160017065635362530918400, 1090356750125690373237899264, 1090317952050623840362954752, 3875451347980454279172325376, 1090736549746484911708045312,
    110864896835982105014960128, 110958823963853739607982080, 110958823963853739607982080, 3186558937691335284951613440, 33035921153439687467702681600, 3186410120159780502723624960,
    111006067624664781585121280, 3875451347980454279172325376, 148270809116030903379292061696, 148270722748057646497441775616, 3875591044335092000962379776, 41674183053723075100947775488,
    148270809116030903379292061696, 41682947021963125442341765120, 3183861501668504542226939904, 3186558937691335284951613440, 1090736549746484911708045312, 41682947021963125442341765120,
    41682924200332301712542924800, 1090775284174992660722876416, 41674160017065635362530918400, 148270722748057646497441775616, 41682924200332301712542924800, 33007956102264062176982466560,
    33035921153439687467702681600, 1090356750125690373237899264, 3875591044335092000962379776, 1090775284174992660722876416, 3183712810111638536806465536, 3186410120159780502723624960,
    110912100504828455942094848, 111006067624664781585121280, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    33, 38, 41, 37, 33, 39,
    46, 46, 37, 39, 40, 39,
    33, 33, 33, 38, 41, 37,
    33, 40, 48, 48, 42, 46,
    48, 47, 38, 38, 39, 47,
    47, 40, 46, 48, 47, 41,
    41, 37, 42, 40, 37, 37,
    33, 33, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 17999388986808774, 18000610753078973, 23110400628829497, 25941373878936780, 24110710379362538,
    20290544268684036, 23547724034863082, 22547723211291336, 20290596012937921, 15519544115936472, 20363447153555385,
    23737411476259634, 19363379775756165, 15520158250863009
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33518933104191236, 38362836141809614, 41736800464692495, 37362768764010393, 33519547239117783, 39816807469388058,
    46073140574932595, 46073139777439322, 37816858805601989, 39816807469388058, 40646422903222825, 39817361246322869,
    33518933104191236, 33520154869016004, 33520154869016004, 38364057906634362, 41738022229521875, 37363990528835141,
    33520769003942551, 40646422903222825, 48904149350933845, 48904148510561460, 42646474906354271, 46073140574932595,
    48904149350933845, 47073443937909548, 38362836141809614, 38364057906634362, 39817361246322869, 47073443937909548,
    47073443148026275, 40817412478654574, 46073139777439322, 48904148510561460, 47073443148026275, 41736800464692495,
    41738022229521875, 37816858805601989, 42646474906354271, 40817412478654574, 37362768764010393, 37363990528835141,
    33519547239117783, 33520769003942551, 0, 1584962500724866, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 166511609 / 250000000000
noncomputable def negativeCeiling : ℝ := 66258279 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 110864896835982105014960128, coefficient := (-110864896835982105014960128) }, { argument := 3183861501668504542226939904, coefficient := (-3183861501668504542226939904) }, { argument := 33007956102264062176982466560, coefficient := (-33007956102264062176982466560) }, { argument := 3183712810111638536806465536, coefficient := (-3183712810111638536806465536) }, { argument := 110912100504828455942094848, coefficient := (-110912100504828455942094848) }, { argument := 1090317952050623840362954752, coefficient := (-1090317952050623840362954752) }, { argument := 41674183053723075100947775488, coefficient := (-41674183053723075100947775488) }, { argument := 41674160017065635362530918400, coefficient := (-41674160017065635362530918400) }, { argument := 1090356750125690373237899264, coefficient := (-1090356750125690373237899264) }, { argument := 1090317952050623840362954752, coefficient := (-1090317952050623840362954752) }, { argument := 3875451347980454279172325376, coefficient := (-3875451347980454279172325376) }, { argument := 1090736549746484911708045312, coefficient := (-1090736549746484911708045312) }, { argument := 110864896835982105014960128, coefficient := (-110864896835982105014960128) }, { argument := 110958823963853739607982080, coefficient := (-110958823963853739607982080) }, { argument := 110958823963853739607982080, coefficient := (-110958823963853739607982080) }, { argument := 3186558937691335284951613440, coefficient := (-3186558937691335284951613440) }, { argument := 33035921153439687467702681600, coefficient := (-33035921153439687467702681600) }, { argument := 3186410120159780502723624960, coefficient := (-3186410120159780502723624960) }, { argument := 111006067624664781585121280, coefficient := (-111006067624664781585121280) }, { argument := 3875451347980454279172325376, coefficient := (-3875451347980454279172325376) }, { argument := 148270809116030903379292061696, coefficient := (-148270809116030903379292061696) }, { argument := 148270722748057646497441775616, coefficient := (-148270722748057646497441775616) }, { argument := 3875591044335092000962379776, coefficient := (-3875591044335092000962379776) }, { argument := 41674183053723075100947775488, coefficient := (-41674183053723075100947775488) }, { argument := 148270809116030903379292061696, coefficient := (-148270809116030903379292061696) }, { argument := 41682947021963125442341765120, coefficient := (-41682947021963125442341765120) }, { argument := 3183861501668504542226939904, coefficient := (-3183861501668504542226939904) }, { argument := 3186558937691335284951613440, coefficient := (-3186558937691335284951613440) }, { argument := 1090736549746484911708045312, coefficient := (-1090736549746484911708045312) }, { argument := 41682947021963125442341765120, coefficient := (-41682947021963125442341765120) }, { argument := 41682924200332301712542924800, coefficient := (-41682924200332301712542924800) }, { argument := 1090775284174992660722876416, coefficient := (-1090775284174992660722876416) }, { argument := 41674160017065635362530918400, coefficient := (-41674160017065635362530918400) }, { argument := 148270722748057646497441775616, coefficient := (-148270722748057646497441775616) }, { argument := 41682924200332301712542924800, coefficient := (-41682924200332301712542924800) }, { argument := 33007956102264062176982466560, coefficient := (-33007956102264062176982466560) }, { argument := 33035921153439687467702681600, coefficient := (-33035921153439687467702681600) }, { argument := 1090356750125690373237899264, coefficient := (-1090356750125690373237899264) }, { argument := 3875591044335092000962379776, coefficient := (-3875591044335092000962379776) }, { argument := 1090775284174992660722876416, coefficient := (-1090775284174992660722876416) }, { argument := 3183712810111638536806465536, coefficient := (-3183712810111638536806465536) }, { argument := 3186410120159780502723624960, coefficient := (-3186410120159780502723624960) }, { argument := 110912100504828455942094848, coefficient := (-110912100504828455942094848) }, { argument := 111006067624664781585121280, coefficient := (-111006067624664781585121280) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 79194614822770031633945853952, coefficient := 79194614822770031633945853952 }, { argument := 79261710205758643553142046720, coefficient := 79261710205758643553142046720 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 171058035545930049354159095808, coefficient := 171058035545930049354159095808 }, { argument := 608585148512808192313737084928, coefficient := 608585148512808192313737084928 }, { argument := 171094766112433809454631223296, coefficient := 171094766112433809454631223296 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 12113011699555126062486650880, coefficient := 12113011699555126062486650880 }, { argument := 463255878383434207845163204608, coefficient := 463255878383434207845163204608 }, { argument := 463255613930911167145031237632, coefficient := 463255613930911167145031237632 }, { argument := 12113446157271550069846310912, coefficient := 12113446157271550069846310912 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 443647441599671689245884416, coefficient := 443647441599671689245884416 }, { argument := 12740840878719679654357106688, coefficient := 12740840878719679654357106688 }, { argument := 132087754511407499289370296320, coefficient := 132087754511407499289370296320 }, { argument := 12740245860542838079060180992, coefficient := 12740245860542838079060180992 }, { argument := 443836336258986475054432256, coefficient := 443836336258986475054432256 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2
