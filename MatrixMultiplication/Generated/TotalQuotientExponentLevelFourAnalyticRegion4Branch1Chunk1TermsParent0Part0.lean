import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 38367, 649691, 14101729, 324845, 19179,
    140893, 8247715, 8250453, 138155
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 362366069696519355827748864, 12272316010488250674125471744, 133187064760221758259376160768, 12272297121022319195544616960, 362281067099827702213902336,
    1330696761741905846186541056, 77897465752522431747357409280, 77923325431382625924547608576, 1304837082881711668996341760
  ]
def positiveScales : Array ℕ := #[
    0, 15, 19, 23, 18, 14,
    17, 22, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    5405641731, 316440081405, 316545130251, 5300592885, 91536914063, 5358466206065,
    5360245060023, 89758060105, 5405641731, 91536914063, 1986834903997, 45768386585,
    2702186847, 1986834903997, 116307041799235, 116345652333237, 1948224369995, 316440081405,
    5358466206065, 116307041799235, 2679228979175, 158182925985, 45768386585, 2679228979175,
    2680118404785, 44878960975, 316545130251, 5360245060023, 116345652333237, 2680118404785,
    158235438087, 2702186847, 158182925985, 158235438087, 2649674745, 5300592885,
    89758060105, 1948224369995, 44878960975, 2649674745, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1521552880339375185985536, 89069964543790463770951680, 89099533165271795059654656, 1491984258858043897282560, 51530701508096489376710656, 3016548301113966179154657280,
    3017549706866765595647410176, 50529295755297072883957760, 1521552880339375185985536, 51530701508096489376710656, 559244308330474024606892032, 51530622192388701987799040,
    1521195959654331935883264, 559244308330474024606892032, 32737521881724965540237148160, 32748389780883964481840873472, 548376409171475083003166720, 89069964543790463770951680,
    3016548301113966179154657280, 32737521881724965540237148160, 3016543658063191096898355200, 89049070815302593617592320, 51530622192388701987799040, 3016543658063191096898355200,
    3017545062274633540923555840, 50529217980946257962598400, 89099533165271795059654656, 3017549706866765595647410176, 32748389780883964481840873472, 3017545062274633540923555840,
    89078632500677548802310144, 1521195959654331935883264, 89049070815302593617592320, 89078632500677548802310144, 1491634274279376751165440, 1491984258858043897282560,
    50529295755297072883957760, 548376409171475083003166720, 50529217980946257962598400, 1491634274279376751165440, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 38, 38, 32, 36, 42,
    42, 36, 32, 36, 40, 35,
    31, 40, 46, 46, 40, 38,
    42, 46, 41, 37, 35, 41,
    41, 35, 38, 42, 46, 41,
    37, 31, 37, 37, 31, 32,
    36, 40, 35, 31, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15227578341406248, 19309394194481380, 23749368725176471, 18309391973893206, 14227239879225015,
    17104240410313222, 22975563049544053, 22976041902589359, 17075928250446576
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32331818751719472, 38203141391934198, 38203620244987242, 32303506591852826, 36413634604794615, 42284957245009330,
    42285436098062374, 36385322444927961, 32331818751719472, 36413634604794615, 40853609137358814, 35413632384206441,
    31331480289538239, 40853609137358814, 46724931775846904, 46725410628901352, 40825296976709524, 38203141391934198,
    42284957245009330, 46724931775846904, 41284955024421156, 37202802929752965, 35413632384206441, 41284955024421156,
    41285433877474200, 35385320224339788, 38203620244987242, 42285436098062374, 46725410628901352, 41285433877474200,
    37203281782806009, 31331480289538239, 37202802929752965, 37203281782806009, 31303168129671593, 32303506591852826,
    36385322444927961, 40825296976709524, 35385320224339788, 31303168129671593, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 87396291 / 1000000000000
noncomputable def negativeCeiling : ℝ := 21849073 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1521552880339375185985536, coefficient := (-1521552880339375185985536) }, { argument := 89069964543790463770951680, coefficient := (-89069964543790463770951680) }, { argument := 89099533165271795059654656, coefficient := (-89099533165271795059654656) }, { argument := 1491984258858043897282560, coefficient := (-1491984258858043897282560) }, { argument := 51530701508096489376710656, coefficient := (-51530701508096489376710656) }, { argument := 3016548301113966179154657280, coefficient := (-3016548301113966179154657280) }, { argument := 3017549706866765595647410176, coefficient := (-3017549706866765595647410176) }, { argument := 50529295755297072883957760, coefficient := (-50529295755297072883957760) }, { argument := 1521552880339375185985536, coefficient := (-1521552880339375185985536) }, { argument := 51530701508096489376710656, coefficient := (-51530701508096489376710656) }, { argument := 559244308330474024606892032, coefficient := (-559244308330474024606892032) }, { argument := 51530622192388701987799040, coefficient := (-51530622192388701987799040) }, { argument := 1521195959654331935883264, coefficient := (-1521195959654331935883264) }, { argument := 559244308330474024606892032, coefficient := (-559244308330474024606892032) }, { argument := 32737521881724965540237148160, coefficient := (-32737521881724965540237148160) }, { argument := 32748389780883964481840873472, coefficient := (-32748389780883964481840873472) }, { argument := 548376409171475083003166720, coefficient := (-548376409171475083003166720) }, { argument := 89069964543790463770951680, coefficient := (-89069964543790463770951680) }, { argument := 3016548301113966179154657280, coefficient := (-3016548301113966179154657280) }, { argument := 32737521881724965540237148160, coefficient := (-32737521881724965540237148160) }, { argument := 3016543658063191096898355200, coefficient := (-3016543658063191096898355200) }, { argument := 89049070815302593617592320, coefficient := (-89049070815302593617592320) }, { argument := 51530622192388701987799040, coefficient := (-51530622192388701987799040) }, { argument := 3016543658063191096898355200, coefficient := (-3016543658063191096898355200) }, { argument := 3017545062274633540923555840, coefficient := (-3017545062274633540923555840) }, { argument := 50529217980946257962598400, coefficient := (-50529217980946257962598400) }, { argument := 89099533165271795059654656, coefficient := (-89099533165271795059654656) }, { argument := 3017549706866765595647410176, coefficient := (-3017549706866765595647410176) }, { argument := 32748389780883964481840873472, coefficient := (-32748389780883964481840873472) }, { argument := 3017545062274633540923555840, coefficient := (-3017545062274633540923555840) }, { argument := 89078632500677548802310144, coefficient := (-89078632500677548802310144) }, { argument := 1521195959654331935883264, coefficient := (-1521195959654331935883264) }, { argument := 89049070815302593617592320, coefficient := (-89049070815302593617592320) }, { argument := 89078632500677548802310144, coefficient := (-89078632500677548802310144) }, { argument := 1491634274279376751165440, coefficient := (-1491634274279376751165440) }, { argument := 1491984258858043897282560, coefficient := (-1491984258858043897282560) }, { argument := 50529295755297072883957760, coefficient := (-50529295755297072883957760) }, { argument := 548376409171475083003166720, coefficient := (-548376409171475083003166720) }, { argument := 50529217980946257962598400, coefficient := (-50529217980946257962598400) }, { argument := 1491634274279376751165440, coefficient := (-1491634274279376751165440) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 362366069696519355827748864, coefficient := 362366069696519355827748864 }, { argument := 12272316010488250674125471744, coefficient := 12272316010488250674125471744 }, { argument := 133187064760221758259376160768, coefficient := 133187064760221758259376160768 }, { argument := 12272297121022319195544616960, coefficient := 12272297121022319195544616960 }, { argument := 362281067099827702213902336, coefficient := 362281067099827702213902336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1330696761741905846186541056, coefficient := 1330696761741905846186541056 }, { argument := 77897465752522431747357409280, coefficient := 77897465752522431747357409280 }, { argument := 77923325431382625924547608576, coefficient := 77923325431382625924547608576 }, { argument := 1304837082881711668996341760, coefficient := 1304837082881711668996341760 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1
