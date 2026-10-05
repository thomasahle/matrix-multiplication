import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

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
def constantNumerator : ℤ := (-60405094054795030423310927134720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1221057, 59799, 1448679, 59799, 926399073515, 148608344126229,
    63159, 5121, 1097601, 1985241, 148608345852693, 1097601,
    32433, 32433, 63159, 63159, 1985241, 63159,
    926397347051, 5121, 1767, 42807, 32433, 18069,
    1767, 18069, 36081, 1767, 42807, 1767,
    272533629, 15825852291, 35187, 2853, 611493, 1106013,
    3956463543, 611493, 18069, 18069, 35187, 35187,
    1106013, 35187, 68132937, 2853, 2257365, 1033092415,
    10839045927, 516547107, 2257365, 1767, 42807, 32433,
    18069, 1767, 18069, 36081, 1767, 42807,
    1767, 3441, 83361, 63159
  ]
def negativeCoefficients : Array ℕ := #[
    5766278650473360375699996672, 282392793309121914133807104, 6841193154037114758531907584, 282392793309121914133807104, 2086065261139263365023006720, 334636241615515681190987169792,
    298259944691563922051825664, 386931820140407250229395456, 5183274173964205456197943296, 9375035558818617333683060736, 334636245503166994725275172864, 5183274173964205456197943296,
    306321024277822406431604736, 306321024277822406431604736, 298259944691563922051825664, 298259944691563922051825664, 9375035558818617333683060736, 298259944691563922051825664,
    2086061373487949830735003648, 386931820140407250229395456, 16688843150461326185201664, 404300684064401805325369344, 306321024277822406431604736, 341313759915886477465092096,
    16688843150461326185201664, 341313759915886477465092096, 340775410136839337910730752, 16688843150461326185201664, 404300684064401805325369344, 16688843150461326185201664,
    628419763205288449233911808, 36491930870050872538832044032, 332331818865468412268642304, 431133170420067129429590016, 5775388095418815921317216256, 10445997441636209823471108096,
    36491935207341572869790367744, 5775388095418815921317216256, 341313759915886477465092096, 341313759915886477465092096, 332331818865468412268642304, 332331818865468412268642304,
    10445997441636209823471108096, 332331818865468412268642304, 628415425914588118275588096, 431133170420067129429590016, 83282068871898723967303680, 19057191383995538687540592640,
    199945106218552903224401068032, 19057224569688127291023949824, 83282068871898723967303680, 16688843150461326185201664, 404300684064401805325369344, 306321024277822406431604736,
    341313759915886477465092096, 16688843150461326185201664, 341313759915886477465092096, 340775410136839337910730752, 16688843150461326185201664, 404300684064401805325369344,
    16688843150461326185201664, 16249663067554449180327936, 393661192378496494658912256, 298259944691563922051825664
  ]
def negativeScales : Array ℕ := #[
    20, 15, 20, 15, 39, 47,
    15, 12, 20, 20, 47, 20,
    14, 14, 15, 15, 20, 15,
    39, 12, 10, 15, 14, 14,
    10, 14, 15, 10, 15, 10,
    28, 33, 15, 11, 19, 20,
    31, 19, 14, 14, 15, 15,
    20, 15, 26, 11, 21, 29,
    33, 28, 21, 10, 15, 14,
    14, 10, 14, 15, 10, 15,
    10, 11, 16, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20219699117477445, 15867833740861174, 20466306525563460, 15867833740861174, 39752842854499267, 47078508451645252,
    15946700718514816, 12322209843748895, 20065922270355686, 20920882730822016, 47078508468405826, 20065922270355686,
    14985174875126365, 14985174875126365, 15946700718514816, 15946700718514816, 20920882730822016, 15946700718514816,
    39752840165848710, 12322209843748895, 10787086325046961, 15385559111679018, 14985174875126365, 14141229044304149,
    10787086325046961, 14141229044304149, 15138951703593084, 10787086325046961, 15385559111679018, 10787086325046961,
    28021859019807151, 33881564149150680, 15102754896489514, 11478264031581849, 19221976458188511, 20076936912333782,
    31881564320623869, 19221976458188511, 14141229044304149, 14141229044304149, 15102754896489514, 15102754896489514,
    20076936912333782, 15102754896489514, 26021849062435113, 11478264031581849, 21106208280328534, 29944322179321029,
    33335518722450813, 28944324691590501, 21106208280328534, 10787086325046961, 15385559111679018, 14985174875126365,
    14141229044304149, 10787086325046961, 14141229044304149, 15138951703593084, 10787086325046961, 15385559111679018,
    10787086325046961, 11748612176955137, 16347084963864379, 15946700718514816
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
noncomputable def negativeCeiling : ℝ := 131084319 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5766278650473360375699996672, coefficient := (-5766278650473360375699996672) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 2086065261139263365023006720, coefficient := (-2086065261139263365023006720) }, { argument := 334636241615515681190987169792, coefficient := (-334636241615515681190987169792) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 386931820140407250229395456, coefficient := (-386931820140407250229395456) }, { argument := 5183274173964205456197943296, coefficient := (-5183274173964205456197943296) }, { argument := 9375035558818617333683060736, coefficient := (-9375035558818617333683060736) }, { argument := 334636245503166994725275172864, coefficient := (-334636245503166994725275172864) }, { argument := 5183274173964205456197943296, coefficient := (-5183274173964205456197943296) }, { argument := 306321024277822406431604736, coefficient := (-306321024277822406431604736) }, { argument := 306321024277822406431604736, coefficient := (-306321024277822406431604736) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 9375035558818617333683060736, coefficient := (-9375035558818617333683060736) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 2086061373487949830735003648, coefficient := (-2086061373487949830735003648) }, { argument := 386931820140407250229395456, coefficient := (-386931820140407250229395456) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 306321024277822406431604736, coefficient := (-306321024277822406431604736) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 340775410136839337910730752, coefficient := (-340775410136839337910730752) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 628419763205288449233911808, coefficient := (-628419763205288449233911808) }, { argument := 36491930870050872538832044032, coefficient := (-36491930870050872538832044032) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 36491935207341572869790367744, coefficient := (-36491935207341572869790367744) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 628415425914588118275588096, coefficient := (-628415425914588118275588096) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 83282068871898723967303680, coefficient := (-83282068871898723967303680) }, { argument := 19057191383995538687540592640, coefficient := (-19057191383995538687540592640) }, { argument := 199945106218552903224401068032, coefficient := (-199945106218552903224401068032) }, { argument := 19057224569688127291023949824, coefficient := (-19057224569688127291023949824) }, { argument := 83282068871898723967303680, coefficient := (-83282068871898723967303680) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 306321024277822406431604736, coefficient := (-306321024277822406431604736) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 340775410136839337910730752, coefficient := (-340775410136839337910730752) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }] }

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
def constantNumerator : ℤ := (-12820083727793705716547265232896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35187, 3441, 35187, 70263, 3441, 83361,
    3441, 13374609, 782383983, 3441, 279, 59799,
    108159, 195596019, 59799, 1767, 1767, 3441,
    3441, 108159, 3441, 3343629, 279, 3441,
    83361, 63159, 35187, 3441, 35187, 70263,
    3441, 83361, 3441, 108159, 2620239, 1985241,
    1106013, 108159, 1106013, 2208537, 108159, 2620239,
    108159, 136195479, 7900414569, 35187, 2853, 611493,
    1106013, 1975103877, 611493, 18069, 18069, 35187,
    35187, 1106013, 35187, 34048635, 2853, 3441,
    83361, 63159, 35187, 3441
  ]
def negativeCoefficients : Array ℕ := #[
    332331818865468412268642304, 16249663067554449180327936, 332331818865468412268642304, 331807636185869881649922048, 16249663067554449180327936, 393661192378496494658912256,
    16249663067554449180327936, 30839748663616554053664768, 1804054637721315572308770816, 16249663067554449180327936, 21080643979530096233938944, 282392793309121914133807104,
    510766436420697956668145664, 1804054852164715429182308352, 282392793309121914133807104, 16688843150461326185201664, 16688843150461326185201664, 16249663067554449180327936,
    16249663067554449180327936, 510766436420697956668145664, 16249663067554449180327936, 30839534220216697180127232, 21080643979530096233938944, 16249663067554449180327936,
    393661192378496494658912256, 298259944691563922051825664, 332331818865468412268642304, 16249663067554449180327936, 332331818865468412268642304, 331807636185869881649922048,
    16249663067554449180327936, 393661192378496494658912256, 16249663067554449180327936, 510766436420697956668145664, 12373728830707876305089593344, 9375035558818617333683060736,
    10445997441636209823471108096, 510766436420697956668145664, 10445997441636209823471108096, 10429521104977477631320522752, 510766436420697956668145664, 12373728830707876305089593344,
    510766436420697956668145664, 628090786277320922304086016, 36434231407637337865375973376, 332331818865468412268642304, 431133170420067129429590016, 5775388095418815921317216256,
    10445997441636209823471108096, 36434235738010509168693215232, 5775388095418815921317216256, 341313759915886477465092096, 341313759915886477465092096, 332331818865468412268642304,
    332331818865468412268642304, 10445997441636209823471108096, 332331818865468412268642304, 628086455904149618986844160, 431133170420067129429590016, 16249663067554449180327936,
    393661192378496494658912256, 298259944691563922051825664, 332331818865468412268642304, 16249663067554449180327936
  ]
def negativeScales : Array ℕ := #[
    15, 11, 15, 16, 11, 16,
    11, 23, 29, 11, 8, 15,
    16, 27, 15, 10, 10, 11,
    11, 16, 11, 21, 8, 11,
    16, 15, 15, 11, 15, 16,
    11, 16, 11, 16, 21, 20,
    20, 16, 20, 21, 16, 21,
    16, 27, 32, 15, 11, 19,
    20, 30, 19, 14, 14, 15,
    15, 20, 15, 25, 11, 11,
    16, 15, 15, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15102754896489514, 11748612176955137, 15102754896489514, 16100477555778448, 11748612176955137, 16347084963864379,
    11748612176955137, 23672993379912215, 29543301594774845, 11748612176955137, 8124121311829188, 15867833740861174,
    16722794192703879, 27543301766264336, 15867833740861174, 10787086325046961, 10787086325046961, 11748612176955137,
    11748612176955137, 16722794192703879, 11748612176955137, 21672983348134433, 8124121311829188, 11748612176955137,
    16347084963864379, 15946700718514816, 15102754896489514, 11748612176955137, 15102754896489514, 16100477555778448,
    11748612176955137, 16347084963864379, 11748612176955137, 16722794192703879, 21321266979708647, 20920882730822016,
    20076936912333782, 16722794192703879, 20076936912333782, 21074659571622716, 16722794192703879, 21321266979708647,
    16722794192703879, 27021103573076384, 32879281216723208, 15102754896489514, 11478264031581849, 19221976458188511,
    20076936912333782, 30879281388194037, 19221976458188511, 14141229044304149, 14141229044304149, 15102754896489514,
    15102754896489514, 20076936912333782, 15102754896489514, 25021093626378276, 11478264031581849, 11748612176955137,
    16347084963864379, 15946700718514816, 15102754896489514, 11748612176955137
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
noncomputable def negativeCeiling : ℝ := 13958857 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 30839748663616554053664768, coefficient := (-30839748663616554053664768) }, { argument := 1804054637721315572308770816, coefficient := (-1804054637721315572308770816) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 1804054852164715429182308352, coefficient := (-1804054852164715429182308352) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 30839534220216697180127232, coefficient := (-30839534220216697180127232) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 9375035558818617333683060736, coefficient := (-9375035558818617333683060736) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 10429521104977477631320522752, coefficient := (-10429521104977477631320522752) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 628090786277320922304086016, coefficient := (-628090786277320922304086016) }, { argument := 36434231407637337865375973376, coefficient := (-36434231407637337865375973376) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 36434235738010509168693215232, coefficient := (-36434235738010509168693215232) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 341313759915886477465092096, coefficient := (-341313759915886477465092096) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 628086455904149618986844160, coefficient := (-628086455904149618986844160) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
