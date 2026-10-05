import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-84385336851473339424683136647168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1081437357585, 51801774065427, 51807375706293, 1076941957671, 31508539191, 694382537757,
    28985868073453, 1389202540927, 63769752627, 31508539191, 2229958867035, 2230442166621,
    31753148397, 3585614649341, 172100910991701, 172119871986059, 3570279122211, 2229958867035,
    98545268262705, 1030042096965105, 770124748785, 2256360141315, 694382537757, 98545268262705,
    98569663821495, 700535989353, 1081437357585, 3585614649341, 540922802425, 540922802425,
    6477559350771, 809782462583, 538674784347, 2230442166621, 98569663821495, 1030310133347607,
    49300181737221, 2256843295947, 28985868073453, 1030042096965105, 1030310133347607, 29256173517579,
    51801774065427, 172100910991701, 6477559350771, 31753148397, 700535989353, 29256173517579,
    350377404111, 64259067135, 1389202540927, 770124748785, 49300181737221, 350377404111,
    51807375706293, 172119871986059, 809782462583, 63769752627, 2256360141315, 2256843295947,
    64259067135, 1076941957671, 3570279122211, 538674784347
  ]
def negativeCoefficients : Array ℕ := #[
    304397555040271239751925760, 14580903148636728804992090112, 14582479870369027613899358208, 303132212454173004766642176, 17737730669947033686638592, 781805234573751142336954368,
    8158796540913330473735815168, 782051505707622927354036224, 17949589635529119274893312, 17737730669947033686638592, 627677620164397464771624960, 627813656904111084458213376,
    17875433411071157798436864, 1009260799916644955058077696, 48442099913271720175894265856, 48447436958717049105708744704, 1004944232774882571809980416, 627677620164397464771624960,
    27738027089190237732580884480, 289931075254248199173313658880, 27746668253255382736966778880, 635108918227492106026352640, 781805234573751142336954368, 27738027089190237732580884480,
    27744893828532496421848350720, 788733405152448138310582272, 304397555040271239751925760, 1009260799916644955058077696, 304512466429679303760281600, 304512466429679303760281600,
    14586166939201273795820126208, 14587743986959845679192604672, 303246944757378936433803264, 627813656904111084458213376, 27744893828532496421848350720, 290006520788770558106709000192,
    27753535012630778468685053952, 635244914166281951596511232, 8158796540913330473735815168, 289931075254248199173313658880, 290006520788770558106709000192, 8234880759503459850412621824,
    14580903148636728804992090112, 48442099913271720175894265856, 14586166939201273795820126208, 17875433411071157798436864, 788733405152448138310582272, 8234880759503459850412621824,
    788979773296670646655254528, 18087319425272605373890560, 782051505707622927354036224, 27746668253255382736966778880, 27753535012630778468685053952, 788979773296670646655254528,
    14582479870369027613899358208, 48447436958717049105708744704, 14587743986959845679192604672, 17949589635529119274893312, 635108918227492106026352640, 635244914166281951596511232,
    18087319425272605373890560, 303132212454173004766642176, 1004944232774882571809980416, 303246944757378936433803264
  ]
def negativeScales : Array ℕ := #[
    39, 45, 45, 39, 34, 39,
    44, 40, 35, 34, 41, 41,
    34, 41, 47, 47, 41, 41,
    46, 49, 39, 41, 39, 46,
    46, 39, 39, 41, 38, 38,
    42, 39, 38, 41, 46, 49,
    45, 41, 44, 49, 49, 44,
    45, 47, 42, 34, 39, 44,
    38, 35, 40, 39, 45, 38,
    45, 47, 39, 35, 41, 41,
    35, 39, 41, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39976087254136967, 45558066740552835, 45558222739507065, 39970077650423725, 34875023820861049, 39336939711289710,
    44720414925975098, 40337394093251096, 35892153237430688, 34875023820861049, 41020154237640600, 41020466879447224,
    34886180597752412, 41705357586959668, 47290248062522462, 47290407000819688, 41699174006387791, 41020154237640600,
    46485851834202745, 49871624726274578, 39486301203693492, 41037134495667826, 39336939711289710, 46485851834202745,
    46486208939080532, 39349668213371203, 39976087254136967, 41705357586959668, 38976631775106033, 38976631775106033,
    42558587467839032, 39558743442743366, 38970623591902198, 41020466879447224, 46486208939080532, 49872000093918087,
    45486658198412989, 41037443387036859, 44720414925975098, 49871624726274578, 49872000093918087, 44733806322095725,
    45558066740552835, 47290248062522462, 42558587467839032, 34886180597752412, 39349668213371203, 44733806322095725,
    38350118782090089, 35903180990492517, 40337394093251096, 39486301203693492, 45486658198412989, 38350118782090089,
    45558222739507065, 47290407000819688, 39558743442743366, 35892153237430688, 41037134495667826, 41037443387036859,
    35903180990492517, 39970077650423725, 41699174006387791, 38970623591902198
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
noncomputable def negativeCeiling : ℝ := 1012632981 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 304397555040271239751925760, coefficient := (-304397555040271239751925760) }, { argument := 14580903148636728804992090112, coefficient := (-14580903148636728804992090112) }, { argument := 14582479870369027613899358208, coefficient := (-14582479870369027613899358208) }, { argument := 303132212454173004766642176, coefficient := (-303132212454173004766642176) }, { argument := 17737730669947033686638592, coefficient := (-17737730669947033686638592) }, { argument := 781805234573751142336954368, coefficient := (-781805234573751142336954368) }, { argument := 8158796540913330473735815168, coefficient := (-8158796540913330473735815168) }, { argument := 782051505707622927354036224, coefficient := (-782051505707622927354036224) }, { argument := 17949589635529119274893312, coefficient := (-17949589635529119274893312) }, { argument := 17737730669947033686638592, coefficient := (-17737730669947033686638592) }, { argument := 627677620164397464771624960, coefficient := (-627677620164397464771624960) }, { argument := 627813656904111084458213376, coefficient := (-627813656904111084458213376) }, { argument := 17875433411071157798436864, coefficient := (-17875433411071157798436864) }, { argument := 1009260799916644955058077696, coefficient := (-1009260799916644955058077696) }, { argument := 48442099913271720175894265856, coefficient := (-48442099913271720175894265856) }, { argument := 48447436958717049105708744704, coefficient := (-48447436958717049105708744704) }, { argument := 1004944232774882571809980416, coefficient := (-1004944232774882571809980416) }, { argument := 627677620164397464771624960, coefficient := (-627677620164397464771624960) }, { argument := 27738027089190237732580884480, coefficient := (-27738027089190237732580884480) }, { argument := 289931075254248199173313658880, coefficient := (-289931075254248199173313658880) }, { argument := 27746668253255382736966778880, coefficient := (-27746668253255382736966778880) }, { argument := 635108918227492106026352640, coefficient := (-635108918227492106026352640) }, { argument := 781805234573751142336954368, coefficient := (-781805234573751142336954368) }, { argument := 27738027089190237732580884480, coefficient := (-27738027089190237732580884480) }, { argument := 27744893828532496421848350720, coefficient := (-27744893828532496421848350720) }, { argument := 788733405152448138310582272, coefficient := (-788733405152448138310582272) }, { argument := 304397555040271239751925760, coefficient := (-304397555040271239751925760) }, { argument := 1009260799916644955058077696, coefficient := (-1009260799916644955058077696) }, { argument := 304512466429679303760281600, coefficient := (-304512466429679303760281600) }, { argument := 304512466429679303760281600, coefficient := (-304512466429679303760281600) }, { argument := 14586166939201273795820126208, coefficient := (-14586166939201273795820126208) }, { argument := 14587743986959845679192604672, coefficient := (-14587743986959845679192604672) }, { argument := 303246944757378936433803264, coefficient := (-303246944757378936433803264) }, { argument := 627813656904111084458213376, coefficient := (-627813656904111084458213376) }, { argument := 27744893828532496421848350720, coefficient := (-27744893828532496421848350720) }, { argument := 290006520788770558106709000192, coefficient := (-290006520788770558106709000192) }, { argument := 27753535012630778468685053952, coefficient := (-27753535012630778468685053952) }, { argument := 635244914166281951596511232, coefficient := (-635244914166281951596511232) }, { argument := 8158796540913330473735815168, coefficient := (-8158796540913330473735815168) }, { argument := 289931075254248199173313658880, coefficient := (-289931075254248199173313658880) }, { argument := 290006520788770558106709000192, coefficient := (-290006520788770558106709000192) }, { argument := 8234880759503459850412621824, coefficient := (-8234880759503459850412621824) }, { argument := 14580903148636728804992090112, coefficient := (-14580903148636728804992090112) }, { argument := 48442099913271720175894265856, coefficient := (-48442099913271720175894265856) }, { argument := 14586166939201273795820126208, coefficient := (-14586166939201273795820126208) }, { argument := 17875433411071157798436864, coefficient := (-17875433411071157798436864) }, { argument := 788733405152448138310582272, coefficient := (-788733405152448138310582272) }, { argument := 8234880759503459850412621824, coefficient := (-8234880759503459850412621824) }, { argument := 788979773296670646655254528, coefficient := (-788979773296670646655254528) }, { argument := 18087319425272605373890560, coefficient := (-18087319425272605373890560) }, { argument := 782051505707622927354036224, coefficient := (-782051505707622927354036224) }, { argument := 27746668253255382736966778880, coefficient := (-27746668253255382736966778880) }, { argument := 27753535012630778468685053952, coefficient := (-27753535012630778468685053952) }, { argument := 788979773296670646655254528, coefficient := (-788979773296670646655254528) }, { argument := 14582479870369027613899358208, coefficient := (-14582479870369027613899358208) }, { argument := 48447436958717049105708744704, coefficient := (-48447436958717049105708744704) }, { argument := 14587743986959845679192604672, coefficient := (-14587743986959845679192604672) }, { argument := 17949589635529119274893312, coefficient := (-17949589635529119274893312) }, { argument := 635108918227492106026352640, coefficient := (-635108918227492106026352640) }, { argument := 635244914166281951596511232, coefficient := (-635244914166281951596511232) }, { argument := 18087319425272605373890560, coefficient := (-18087319425272605373890560) }, { argument := 303132212454173004766642176, coefficient := (-303132212454173004766642176) }, { argument := 1004944232774882571809980416, coefficient := (-1004944232774882571809980416) }, { argument := 303246944757378936433803264, coefficient := (-303246944757378936433803264) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 88497419179486859200041276407808
def positiveArguments : Array ℕ := #[
    11, 1576059, 10471841, 3153257, 2066409, 9176505,
    36715491, 2085513, 136701, 3020385, 126278059, 1510663,
    276639, 342661, 16434381, 16436179, 341211
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 59541825573000401326820032512, 197807483809360593616942137344, 59563340674696355430413631488, 19516681203000361392776675328, 693357114270171418427318599680,
    693536016402008452066594258944, 19697113381577844797101572096, 2582208882299053481429827584, 114106919114897866870153543680, 1192662546686871095208342192128, 114142469089780909559322247168,
    2612781482909151564543295488, 3236341642773190997140570112, 155218340002219445553412964352, 155235321632091844797601415168, 3222646779972869026020851712
  ]
def positiveScales : Array ℕ := #[
    3, 20, 23, 21, 20, 23,
    25, 20, 17, 21, 26, 20,
    18, 18, 23, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 20587890112629742, 23320011761502957, 21588411328154412, 20978694400358493, 23129513357032342,
    25129885557621023, 20991970873303813, 17060664271073279, 21526301026884157, 26912028749262081, 20526750428070163,
    18077645033457172, 18386422475140169, 23970213781727482, 23970371610839463, 18380304631613657
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 55364943 / 50000000000
noncomputable def negativeCeiling : ℝ := 108830739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 59541825573000401326820032512, coefficient := 59541825573000401326820032512 }, { argument := 197807483809360593616942137344, coefficient := 197807483809360593616942137344 }, { argument := 59563340674696355430413631488, coefficient := 59563340674696355430413631488 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 19516681203000361392776675328, coefficient := 19516681203000361392776675328 }, { argument := 693357114270171418427318599680, coefficient := 693357114270171418427318599680 }, { argument := 693536016402008452066594258944, coefficient := 693536016402008452066594258944 }, { argument := 19697113381577844797101572096, coefficient := 19697113381577844797101572096 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2582208882299053481429827584, coefficient := 2582208882299053481429827584 }, { argument := 114106919114897866870153543680, coefficient := 114106919114897866870153543680 }, { argument := 1192662546686871095208342192128, coefficient := 1192662546686871095208342192128 }, { argument := 114142469089780909559322247168, coefficient := 114142469089780909559322247168 }, { argument := 2612781482909151564543295488, coefficient := 2612781482909151564543295488 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3236341642773190997140570112, coefficient := 3236341642773190997140570112 }, { argument := 155218340002219445553412964352, coefficient := 155218340002219445553412964352 }, { argument := 155235321632091844797601415168, coefficient := 155235321632091844797601415168 }, { argument := 3222646779972869026020851712, coefficient := 3222646779972869026020851712 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3
