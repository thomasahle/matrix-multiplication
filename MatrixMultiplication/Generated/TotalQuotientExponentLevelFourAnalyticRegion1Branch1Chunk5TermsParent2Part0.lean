import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-138415590913166531523878884212736)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    470259, 2257365, 9018645, 4496705, 9018645, 73616409,
    1033092415, 4125402175, 2054572355, 4125402175, 28652865725, 40661841,
    926399073515, 272533629, 13374609, 136195479, 273671571, 3591587147,
    40661841, 13374609, 18404109, 10839045927, 43282081575, 21554588299,
    43282081575, 3767708153667, 2397386415, 148608344126229, 15825852291, 782383983,
    7900414569, 16075868781, 472942688949, 2397386415, 782383983, 3441,
    83361, 63159, 35187, 3441, 35187, 70263,
    3441, 83361, 3441, 28652865725, 3767708153667, 3441,
    279, 59799, 108159, 3767708248899, 59799, 1767,
    1767, 3441, 3441, 108159, 3441, 28652770493,
    279, 279, 6759, 5121
  ]
def negativeCoefficients : Array ℕ := #[
    8882941359471185954189869056, 83282068871898723967303680, 83182318103320139566940160, 82949566309970109299425280, 83182318103320139566940160, 347643662450823295736337137664,
    19057191383995538687540592640, 19025059530837436138730291200, 18950085206801863524839587840, 19025059530837436138730291200, 64520517701103428357324800, 750078574492870067991085056,
    2086065261139263365023006720, 628419763205288449233911808, 30839748663616554053664768, 628090786277320922304086016, 631043678810879098557038592, 64700282147591451362459648,
    750078574492870067991085056, 30839748663616554053664768, 347643789954718333216757907456, 199945106218552903224401068032, 199603370447861156475096268800, 198805986982913747393385070592,
    199603370447861156475096268800, 8484124518447740341155004416, 44223973643293037699939696640, 334636241615515681190987169792, 36491930870050872538832044032, 1804054637721315572308770816,
    36434231407637337865375973376, 37068429645705517960645312512, 8519778070873267186031394816, 44223973643293037699939696640, 1804054637721315572308770816, 16249663067554449180327936,
    393661192378496494658912256, 298259944691563922051825664, 332331818865468412268642304, 16249663067554449180327936, 332331818865468412268642304, 331807636185869881649922048,
    16249663067554449180327936, 393661192378496494658912256, 16249663067554449180327936, 64520517701103428357324800, 8484124518447740341155004416, 16249663067554449180327936,
    21080643979530096233938944, 282392793309121914133807104, 510766436420697956668145664, 8484124732891140198028541952, 282392793309121914133807104, 16688843150461326185201664,
    16688843150461326185201664, 16249663067554449180327936, 16249663067554449180327936, 510766436420697956668145664, 16249663067554449180327936, 64520303257703571483787264,
    21080643979530096233938944, 21080643979530096233938944, 510695600923454911989940224, 386931820140407250229395456
  ]
def negativeScales : Array ℕ := #[
    18, 21, 23, 22, 23, 26,
    29, 31, 30, 31, 34, 25,
    39, 28, 23, 27, 28, 31,
    25, 23, 24, 33, 35, 34,
    35, 41, 31, 47, 33, 29,
    32, 33, 38, 31, 29, 11,
    16, 15, 15, 11, 15, 16,
    11, 16, 11, 34, 41, 11,
    8, 15, 16, 41, 15, 10,
    10, 11, 11, 16, 11, 34,
    8, 8, 12, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18843096030826774, 21106208280328534, 23104479262380694, 22100436810458735, 23104479262380694, 26133524041151017,
    29944322179321029, 31941887633966610, 30936191000403848, 31941887633966610, 34737960386823697, 25277172200137984,
    39752842854499267, 28021859019807151, 23672993379912215, 27021103573076384, 28027870334439218, 31741974375966605,
    25277172200137984, 23672993379912215, 24133524570282491, 33335518722450813, 35333050833567806, 34327275955618125,
    35333050833567806, 41776824357299219, 31158815317864456, 47078508451645252, 33881564149150680, 29543301594774845,
    32879281216723208, 33904177660164140, 38782874413025574, 31158815317864456, 29543301594774845, 11748612176955137,
    16347084963864379, 15946700718514816, 15102754896489514, 11748612176955137, 15102754896489514, 16100477555778448,
    11748612176955137, 16347084963864379, 11748612176955137, 34737960386823697, 41776824357299219, 11748612176955137,
    8124121311829188, 15867833740861174, 16722794192703879, 41776824393764553, 15867833740861174, 10787086325046961,
    10787086325046961, 11748612176955137, 11748612176955137, 16722794192703879, 11748612176955137, 34737955591807230,
    8124121311829188, 8124121311829188, 12722594099078657, 12322209843748895
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
noncomputable def negativeCeiling : ℝ := 861549001 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8882941359471185954189869056, coefficient := (-8882941359471185954189869056) }, { argument := 83282068871898723967303680, coefficient := (-83282068871898723967303680) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 82949566309970109299425280, coefficient := (-82949566309970109299425280) }, { argument := 83182318103320139566940160, coefficient := (-83182318103320139566940160) }, { argument := 347643662450823295736337137664, coefficient := (-347643662450823295736337137664) }, { argument := 19057191383995538687540592640, coefficient := (-19057191383995538687540592640) }, { argument := 19025059530837436138730291200, coefficient := (-19025059530837436138730291200) }, { argument := 18950085206801863524839587840, coefficient := (-18950085206801863524839587840) }, { argument := 19025059530837436138730291200, coefficient := (-19025059530837436138730291200) }, { argument := 64520517701103428357324800, coefficient := (-64520517701103428357324800) }, { argument := 750078574492870067991085056, coefficient := (-750078574492870067991085056) }, { argument := 2086065261139263365023006720, coefficient := (-2086065261139263365023006720) }, { argument := 628419763205288449233911808, coefficient := (-628419763205288449233911808) }, { argument := 30839748663616554053664768, coefficient := (-30839748663616554053664768) }, { argument := 628090786277320922304086016, coefficient := (-628090786277320922304086016) }, { argument := 631043678810879098557038592, coefficient := (-631043678810879098557038592) }, { argument := 64700282147591451362459648, coefficient := (-64700282147591451362459648) }, { argument := 750078574492870067991085056, coefficient := (-750078574492870067991085056) }, { argument := 30839748663616554053664768, coefficient := (-30839748663616554053664768) }, { argument := 347643789954718333216757907456, coefficient := (-347643789954718333216757907456) }, { argument := 199945106218552903224401068032, coefficient := (-199945106218552903224401068032) }, { argument := 199603370447861156475096268800, coefficient := (-199603370447861156475096268800) }, { argument := 198805986982913747393385070592, coefficient := (-198805986982913747393385070592) }, { argument := 199603370447861156475096268800, coefficient := (-199603370447861156475096268800) }, { argument := 8484124518447740341155004416, coefficient := (-8484124518447740341155004416) }, { argument := 44223973643293037699939696640, coefficient := (-44223973643293037699939696640) }, { argument := 334636241615515681190987169792, coefficient := (-334636241615515681190987169792) }, { argument := 36491930870050872538832044032, coefficient := (-36491930870050872538832044032) }, { argument := 1804054637721315572308770816, coefficient := (-1804054637721315572308770816) }, { argument := 36434231407637337865375973376, coefficient := (-36434231407637337865375973376) }, { argument := 37068429645705517960645312512, coefficient := (-37068429645705517960645312512) }, { argument := 8519778070873267186031394816, coefficient := (-8519778070873267186031394816) }, { argument := 44223973643293037699939696640, coefficient := (-44223973643293037699939696640) }, { argument := 1804054637721315572308770816, coefficient := (-1804054637721315572308770816) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 298259944691563922051825664, coefficient := (-298259944691563922051825664) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 332331818865468412268642304, coefficient := (-332331818865468412268642304) }, { argument := 331807636185869881649922048, coefficient := (-331807636185869881649922048) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 64520517701103428357324800, coefficient := (-64520517701103428357324800) }, { argument := 8484124518447740341155004416, coefficient := (-8484124518447740341155004416) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 8484124732891140198028541952, coefficient := (-8484124732891140198028541952) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 64520303257703571483787264, coefficient := (-64520303257703571483787264) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 386931820140407250229395456, coefficient := (-386931820140407250229395456) }] }

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
def constantNumerator : ℤ := (-54812408644175302420787307216896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2853, 279, 2853, 5697, 279, 6759,
    279, 59799, 1448679, 1097601, 611493, 59799,
    611493, 1221057, 59799, 1448679, 59799, 108159,
    2620239, 1985241, 1106013, 108159, 1106013, 2208537,
    108159, 2620239, 108159, 40661841, 2397386415, 83361,
    6759, 1448679, 2620239, 599346675, 1448679, 42807,
    42807, 83361, 83361, 2620239, 83361, 10165389,
    6759, 1881063, 516547107, 2062704675, 1027287959, 2062704675,
    3767708248899, 599346675, 148608345852693, 3956463543, 195596019, 1975103877,
    4018967673, 472942700853, 599346675, 195596019, 59799, 1448679,
    1097601, 611493, 59799, 611493
  ]
def negativeCoefficients : Array ℕ := #[
    431133170420067129429590016, 21080643979530096233938944, 431133170420067129429590016, 430453149646533900518817792, 21080643979530096233938944, 510695600923454911989940224,
    21080643979530096233938944, 282392793309121914133807104, 6841193154037114758531907584, 5183274173964205456197943296, 5775388095418815921317216256, 282392793309121914133807104,
    5775388095418815921317216256, 5766278650473360375699996672, 282392793309121914133807104, 6841193154037114758531907584, 282392793309121914133807104, 510766436420697956668145664,
    12373728830707876305089593344, 9375035558818617333683060736, 10445997441636209823471108096, 510766436420697956668145664, 10445997441636209823471108096, 10429521104977477631320522752,
    510766436420697956668145664, 12373728830707876305089593344, 510766436420697956668145664, 750078574492870067991085056, 44223973643293037699939696640, 393661192378496494658912256,
    510695600923454911989940224, 6841193154037114758531907584, 12373728830707876305089593344, 44223978900615098707161907200, 6841193154037114758531907584, 404300684064401805325369344,
    404300684064401805325369344, 393661192378496494658912256, 393661192378496494658912256, 12373728830707876305089593344, 393661192378496494658912256, 750073317170809060768874496,
    510695600923454911989940224, 8883068863366223434610638848, 19057224569688127291023949824, 19025092619684618355238502400, 18950118069676430838405791744, 19025092619684618355238502400,
    8484124732891140198028541952, 44223978900615098707161907200, 334636245503166994725275172864, 36491935207341572869790367744, 1804054852164715429182308352, 36434235738010509168693215232,
    37068434052171508568014454784, 8519778285316667042904932352, 44223978900615098707161907200, 1804054852164715429182308352, 282392793309121914133807104, 6841193154037114758531907584,
    5183274173964205456197943296, 5775388095418815921317216256, 282392793309121914133807104, 5775388095418815921317216256
  ]
def negativeScales : Array ℕ := #[
    11, 8, 11, 12, 8, 12,
    8, 15, 20, 20, 19, 15,
    19, 20, 15, 20, 15, 16,
    21, 20, 20, 16, 20, 21,
    16, 21, 16, 25, 31, 16,
    12, 20, 21, 29, 20, 15,
    15, 16, 16, 21, 16, 23,
    12, 20, 28, 30, 29, 30,
    41, 29, 47, 31, 27, 30,
    31, 38, 29, 27, 15, 20,
    20, 19, 15, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11478264031581849, 8124121311829188, 11478264031581849, 12475986690870773, 8124121311829188, 12722594099078657,
    8124121311829188, 15867833740861174, 20466306525563460, 20065922270355686, 19221976458188511, 15867833740861174,
    19221976458188511, 20219699117477445, 15867833740861174, 20466306525563460, 15867833740861174, 16722794192703879,
    21321266979708647, 20920882730822016, 20076936912333782, 16722794192703879, 20076936912333782, 21074659571622716,
    16722794192703879, 21321266979708647, 16722794192703879, 25277172200137984, 31158815317864456, 16347084963864379,
    12722594099078657, 20466306525563460, 21321266979708647, 29158815489371252, 20466306525563460, 15385559111679018,
    15385559111679018, 16347084963864379, 16347084963864379, 21321266979708647, 16347084963864379, 23277162088211975,
    12722594099078657, 20843116738823689, 28944324691590501, 30941890143135191, 29936193502296121, 30941890143135191,
    41776824393764553, 29158815489371252, 47078508468405826, 31881564320623869, 27543301766264336, 30879281388194037,
    31904177831662820, 38782874449338307, 29158815489371252, 27543301766264336, 15867833740861174, 20466306525563460,
    20065922270355686, 19221976458188511, 15867833740861174, 19221976458188511
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
noncomputable def negativeCeiling : ℝ := 94093061 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 431133170420067129429590016, coefficient := (-431133170420067129429590016) }, { argument := 430453149646533900518817792, coefficient := (-430453149646533900518817792) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 21080643979530096233938944, coefficient := (-21080643979530096233938944) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 5183274173964205456197943296, coefficient := (-5183274173964205456197943296) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 5766278650473360375699996672, coefficient := (-5766278650473360375699996672) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 9375035558818617333683060736, coefficient := (-9375035558818617333683060736) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 10445997441636209823471108096, coefficient := (-10445997441636209823471108096) }, { argument := 10429521104977477631320522752, coefficient := (-10429521104977477631320522752) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 750078574492870067991085056, coefficient := (-750078574492870067991085056) }, { argument := 44223973643293037699939696640, coefficient := (-44223973643293037699939696640) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 44223978900615098707161907200, coefficient := (-44223978900615098707161907200) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 404300684064401805325369344, coefficient := (-404300684064401805325369344) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 12373728830707876305089593344, coefficient := (-12373728830707876305089593344) }, { argument := 393661192378496494658912256, coefficient := (-393661192378496494658912256) }, { argument := 750073317170809060768874496, coefficient := (-750073317170809060768874496) }, { argument := 510695600923454911989940224, coefficient := (-510695600923454911989940224) }, { argument := 8883068863366223434610638848, coefficient := (-8883068863366223434610638848) }, { argument := 19057224569688127291023949824, coefficient := (-19057224569688127291023949824) }, { argument := 19025092619684618355238502400, coefficient := (-19025092619684618355238502400) }, { argument := 18950118069676430838405791744, coefficient := (-18950118069676430838405791744) }, { argument := 19025092619684618355238502400, coefficient := (-19025092619684618355238502400) }, { argument := 8484124732891140198028541952, coefficient := (-8484124732891140198028541952) }, { argument := 44223978900615098707161907200, coefficient := (-44223978900615098707161907200) }, { argument := 334636245503166994725275172864, coefficient := (-334636245503166994725275172864) }, { argument := 36491935207341572869790367744, coefficient := (-36491935207341572869790367744) }, { argument := 1804054852164715429182308352, coefficient := (-1804054852164715429182308352) }, { argument := 36434235738010509168693215232, coefficient := (-36434235738010509168693215232) }, { argument := 37068434052171508568014454784, coefficient := (-37068434052171508568014454784) }, { argument := 8519778285316667042904932352, coefficient := (-8519778285316667042904932352) }, { argument := 44223978900615098707161907200, coefficient := (-44223978900615098707161907200) }, { argument := 1804054852164715429182308352, coefficient := (-1804054852164715429182308352) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6841193154037114758531907584, coefficient := (-6841193154037114758531907584) }, { argument := 5183274173964205456197943296, coefficient := (-5183274173964205456197943296) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 5775388095418815921317216256, coefficient := (-5775388095418815921317216256) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
