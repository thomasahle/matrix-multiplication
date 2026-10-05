import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-332157257590751421822400227966976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    945, 14356765321, 110751, 244713906587, 1742871, 52461,
    244714026525, 52461, 52461, 4494159, 52461, 1742871,
    4494159, 14356645383, 52461, 52461, 110751, 13265696909,
    5651522067, 13265696475, 31395, 52325, 1601145, 52325,
    1643005, 52325, 1601145, 910455, 1643005, 25649715,
    31395, 52325, 1601145, 52325, 31395, 52325,
    805805, 910455, 31395, 503792065, 199861, 8081308163,
    3145181, 94671, 8081312117, 94671, 94671, 8110149,
    94671, 3145181, 8110149, 503788111, 94671, 94671,
    199861, 80955, 134925, 4128705, 134925, 4236645,
    134925, 4128705, 2347695, 4236645
  ]
def negativeCoefficients : Array ℕ := #[
    71402181220989035631083520, 33104446950349444808381038592, 1046013620688592154124091392, 1128543701522013764181869723648, 8230475594365501423239561216, 990960272231297830222823424,
    1128544254638411442325920153600, 990960272231297830222823424, 990960272231297830222823424, 42446131660573923727877603328, 990960272231297830222823424, 8230475594365501423239561216,
    42446131660573923727877603328, 33104170392150605736355823616, 990960272231297830222823424, 990960272231297830222823424, 1046013620688592154124091392, 61177228959930716759036788736,
    208504362393742011012999020544, 61177226958458984761550438400, 593034782918770045935943680, 15814260877833867891625164800, 15122386964428636171366563840, 494195652432308371613286400,
    15517743486374482868657192960, 494195652432308371613286400, 15122386964428636171366563840, 8599004352322165666071183360, 15517743486374482868657192960, 242254708822317563764832993280,
    9488556526700320734975098880, 15814260877833867891625164800, 15122386964428636171366563840, 494195652432308371613286400, 9488556526700320734975098880, 494195652432308371613286400,
    15221226094915097845689221120, 8599004352322165666071183360, 593034782918770045935943680, 18586646578841294437697454080, 1887633775265620324108992512, 596295293854563492661802565632,
    14852697336958433602857598976, 1788284629199008728103256064, 596295585608267762452070924288, 1788284629199008728103256064, 1788284629199008728103256064, 76598191617357540520422801408,
    1788284629199008728103256064, 14852697336958433602857598976, 76598191617357540520422801408, 18586500701989159542563274752, 1788284629199008728103256064, 1788284629199008728103256064,
    1887633775265620324108992512, 3058393428965697026198077440, 81557158105751920698615398400, 77989032438625274168050974720, 2548661190804747521831731200, 80027961391269072185516359680,
    2548661190804747521831731200, 77989032438625274168050974720, 44346704720002606879872122880, 80027961391269072185516359680
  ]
def negativeScales : Array ℕ := #[
    9, 33, 16, 37, 20, 15,
    37, 15, 15, 22, 15, 20,
    22, 33, 15, 15, 16, 33,
    32, 33, 14, 15, 20, 15,
    20, 15, 20, 19, 20, 24,
    14, 15, 20, 15, 14, 15,
    19, 19, 14, 28, 17, 32,
    21, 16, 32, 16, 16, 22,
    16, 21, 22, 28, 16, 16,
    17, 16, 17, 21, 17, 22,
    17, 21, 21, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9884170522387776, 33741011685612747, 16756960200011716, 37832305134124789, 20733034360659112, 15678957687792584,
    37832305841211370, 15678957687792584, 15678957687792584, 22099619736221536, 15678957687792584, 20733034360659112,
    22099619736221536, 33740999633128957, 15678957687792584, 15678957687792584, 16756960200011716, 33626981417949731,
    32395992320237886, 33626981370750578, 14938247200400131, 15675212786070387, 20610672533843301, 15675212786070387,
    20647905440054897, 15675212786070387, 20610672533843301, 19796228187589900, 20647905440054897, 24612439460017861,
    14938247200400131, 15675212786070387, 20610672533843301, 15675212786070387, 14938247200400131, 15675212786070387,
    19620071231847735, 19796228187589900, 14938247200400131, 28908253163176023, 17608637452800154, 32911941707750489,
    21584711613551188, 16530634940792444, 32911942413628204, 16530634940792444, 16530634940792444, 22951296999919123,
    16530634940792444, 21584711613551188, 22951296999919123, 28908241840172971, 16530634940792444, 16530634940792444,
    17608637452800154, 16304832567581158, 17041798161747364, 21977257925950856, 17041798161747364, 22014490815751628,
    17041798161747364, 21977257925950856, 21162813562708730, 22014490815751628
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
noncomputable def negativeCeiling : ℝ := 98696981 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 33104446950349444808381038592, coefficient := (-33104446950349444808381038592) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1128543701522013764181869723648, coefficient := (-1128543701522013764181869723648) }, { argument := 8230475594365501423239561216, coefficient := (-8230475594365501423239561216) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 1128544254638411442325920153600, coefficient := (-1128544254638411442325920153600) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 42446131660573923727877603328, coefficient := (-42446131660573923727877603328) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 8230475594365501423239561216, coefficient := (-8230475594365501423239561216) }, { argument := 42446131660573923727877603328, coefficient := (-42446131660573923727877603328) }, { argument := 33104170392150605736355823616, coefficient := (-33104170392150605736355823616) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 990960272231297830222823424, coefficient := (-990960272231297830222823424) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 61177228959930716759036788736, coefficient := (-61177228959930716759036788736) }, { argument := 208504362393742011012999020544, coefficient := (-208504362393742011012999020544) }, { argument := 61177226958458984761550438400, coefficient := (-61177226958458984761550438400) }, { argument := 593034782918770045935943680, coefficient := (-593034782918770045935943680) }, { argument := 15814260877833867891625164800, coefficient := (-15814260877833867891625164800) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15517743486374482868657192960, coefficient := (-15517743486374482868657192960) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 8599004352322165666071183360, coefficient := (-8599004352322165666071183360) }, { argument := 15517743486374482868657192960, coefficient := (-15517743486374482868657192960) }, { argument := 242254708822317563764832993280, coefficient := (-242254708822317563764832993280) }, { argument := 9488556526700320734975098880, coefficient := (-9488556526700320734975098880) }, { argument := 15814260877833867891625164800, coefficient := (-15814260877833867891625164800) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 9488556526700320734975098880, coefficient := (-9488556526700320734975098880) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15221226094915097845689221120, coefficient := (-15221226094915097845689221120) }, { argument := 8599004352322165666071183360, coefficient := (-8599004352322165666071183360) }, { argument := 593034782918770045935943680, coefficient := (-593034782918770045935943680) }, { argument := 18586646578841294437697454080, coefficient := (-18586646578841294437697454080) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 596295293854563492661802565632, coefficient := (-596295293854563492661802565632) }, { argument := 14852697336958433602857598976, coefficient := (-14852697336958433602857598976) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 596295585608267762452070924288, coefficient := (-596295585608267762452070924288) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 76598191617357540520422801408, coefficient := (-76598191617357540520422801408) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 14852697336958433602857598976, coefficient := (-14852697336958433602857598976) }, { argument := 76598191617357540520422801408, coefficient := (-76598191617357540520422801408) }, { argument := 18586500701989159542563274752, coefficient := (-18586500701989159542563274752) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1788284629199008728103256064, coefficient := (-1788284629199008728103256064) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 3058393428965697026198077440, coefficient := (-3058393428965697026198077440) }, { argument := 81557158105751920698615398400, coefficient := (-81557158105751920698615398400) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 80027961391269072185516359680, coefficient := (-80027961391269072185516359680) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 44346704720002606879872122880, coefficient := (-44346704720002606879872122880) }, { argument := 80027961391269072185516359680, coefficient := (-80027961391269072185516359680) }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4076292182389503872558386403868672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    66140235, 80955, 134925, 4128705, 134925, 80955,
    134925, 2077845, 2347695, 80955, 183219828193, 3120123,
    3022671401891, 49100883, 1477953, 3022672882005, 1477953, 1477953,
    126611307, 1477953, 49100883, 126611307, 183218348079, 1477953,
    1477953, 3120123, 202337760097, 87167515923, 202337739783, 7121357391,
    3819, 121022275821, 60099, 1809, 121022335131, 1809,
    1809, 154971, 1809, 60099, 154971, 7121298081,
    1809, 1809, 3819, 167108032289, 568012283019, 41777007381,
    23541, 23541, 19793946385243, 2598845373316275, 14718938241, 53164519605421091,
    507115513, 1124109637, 14718938241, 14416161921, 507115513, 184223621913,
    7151708055, 324855709443135, 14718938241, 1124109637
  ]
def negativeCoefficients : Array ℕ := #[
    1249353715732487235201914634240, 48934294863451152419169239040, 81557158105751920698615398400, 77989032438625274168050974720, 2548661190804747521831731200, 48934294863451152419169239040,
    2548661190804747521831731200, 78498764676786223672417320960, 44346704720002606879872122880, 3058393428965697026198077440, 422476159988163121908323188736, 29468728555261372066185609216,
    13939611442401036654972936126464, 231872364158503953889197293568, 27917742841826563010070577152, 13939618268222076133607756267520, 27917742841826563010070577152, 27917742841826563010070577152,
    1195809985058237782264689721344, 27917742841826563010070577152, 231872364158503953889197293568, 1195809985058237782264689721344, 422472747077643382590913118208, 27917742841826563010070577152,
    27917742841826563010070577152, 29468728555261372066185609216, 933118219239249934933911666688, 3215913715545166452329740763136, 933118125557460156599953784832, 32841464312299241046974398464,
    1154221926277067204550721536, 1116233474643937255156894138368, 9081904104127449846333308928, 1093473403841432088521736192, 1116234021682132761013647310848, 1093473403841432088521736192,
    1093473403841432088521736192, 46837110797874674458347700224, 1093473403841432088521736192, 9081904104127449846333308928, 46837110797874674458347700224, 32841190793201488118597812224,
    1093473403841432088521736192, 1093473403841432088521736192, 1154221926277067204550721536, 1541299552148187573727120064512, 5238988607787485414855490404352, 1541299526645563891823664955392,
    227674581756383883214064713728, 227674581756383883214064713728, 11143001195596493883038498816, 1463019881857589207307701452800, 33939560846057955250963218432, 14964481917769115903828946845696,
    18709260168237858161495638016, 1296010174033096581905907712, 33939560846057955250963218432, 33241406185230506902570401792, 18709260168237858161495638016, 424790750720117730035342770176,
    32981432045118028505646366720, 1463020051997280904636488744960, 33939560846057955250963218432, 1296010174033096581905907712
  ]
def negativeScales : Array ℕ := #[
    25, 16, 17, 21, 17, 16,
    17, 20, 21, 16, 37, 21,
    41, 25, 20, 41, 20, 20,
    26, 20, 25, 26, 37, 20,
    20, 21, 37, 36, 37, 32,
    11, 36, 15, 10, 36, 10,
    10, 17, 10, 15, 17, 32,
    10, 10, 11, 37, 39, 35,
    14, 14, 44, 51, 33, 55,
    28, 30, 33, 33, 28, 37,
    32, 48, 33, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25979024852605519, 16304832567581158, 17041798161747364, 21977257925950856, 17041798161747364, 16304832567581158,
    17041798161747364, 20986656626663166, 21162813562708730, 16304832567581158, 37414784685229541, 21573171472770842,
    41458961289089540, 25549245633524017, 20495168960767155, 41458961995535038, 20495168960767155, 20495168960767155,
    26915831015024921, 20495168960767155, 25549245633524017, 26915831015024921, 37414773030586188, 20495168960767155,
    20495168960767155, 21573171472770842, 37557974623279282, 36343071545480675, 37557974478437763, 32729505111418701,
    11898979208910875, 36816481664547161, 15875053368150273, 10820976693606152, 36816482371575870, 10820976693606152,
    10820976693606152, 17241638741093964, 10820976693606152, 15875053368150273, 17241638741093964, 32729493095928568,
    10820976693606152, 10820976693606152, 11898979208910875, 37281990124048193, 39047131171482135, 35281990100177097,
    14522887985584760, 14522887985584760, 44170124509530164, 51206792221881583, 33776954554793638, 55561313273964322,
    28917739173159456, 30066135605775057, 33776954554793638, 33746968069656678, 28917739173159456, 37422667105362668,
    32735640698585082, 48206792389657618, 33776954554793638, 30066135605775057
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
noncomputable def negativeCeiling : ℝ := 34963774549 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1249353715732487235201914634240, coefficient := (-1249353715732487235201914634240) }, { argument := 48934294863451152419169239040, coefficient := (-48934294863451152419169239040) }, { argument := 81557158105751920698615398400, coefficient := (-81557158105751920698615398400) }, { argument := 77989032438625274168050974720, coefficient := (-77989032438625274168050974720) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 48934294863451152419169239040, coefficient := (-48934294863451152419169239040) }, { argument := 2548661190804747521831731200, coefficient := (-2548661190804747521831731200) }, { argument := 78498764676786223672417320960, coefficient := (-78498764676786223672417320960) }, { argument := 44346704720002606879872122880, coefficient := (-44346704720002606879872122880) }, { argument := 3058393428965697026198077440, coefficient := (-3058393428965697026198077440) }, { argument := 422476159988163121908323188736, coefficient := (-422476159988163121908323188736) }, { argument := 29468728555261372066185609216, coefficient := (-29468728555261372066185609216) }, { argument := 13939611442401036654972936126464, coefficient := (-13939611442401036654972936126464) }, { argument := 231872364158503953889197293568, coefficient := (-231872364158503953889197293568) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 13939618268222076133607756267520, coefficient := (-13939618268222076133607756267520) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 1195809985058237782264689721344, coefficient := (-1195809985058237782264689721344) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 231872364158503953889197293568, coefficient := (-231872364158503953889197293568) }, { argument := 1195809985058237782264689721344, coefficient := (-1195809985058237782264689721344) }, { argument := 422472747077643382590913118208, coefficient := (-422472747077643382590913118208) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 27917742841826563010070577152, coefficient := (-27917742841826563010070577152) }, { argument := 29468728555261372066185609216, coefficient := (-29468728555261372066185609216) }, { argument := 933118219239249934933911666688, coefficient := (-933118219239249934933911666688) }, { argument := 3215913715545166452329740763136, coefficient := (-3215913715545166452329740763136) }, { argument := 933118125557460156599953784832, coefficient := (-933118125557460156599953784832) }, { argument := 32841464312299241046974398464, coefficient := (-32841464312299241046974398464) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 1116233474643937255156894138368, coefficient := (-1116233474643937255156894138368) }, { argument := 9081904104127449846333308928, coefficient := (-9081904104127449846333308928) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1116234021682132761013647310848, coefficient := (-1116234021682132761013647310848) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 46837110797874674458347700224, coefficient := (-46837110797874674458347700224) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 9081904104127449846333308928, coefficient := (-9081904104127449846333308928) }, { argument := 46837110797874674458347700224, coefficient := (-46837110797874674458347700224) }, { argument := 32841190793201488118597812224, coefficient := (-32841190793201488118597812224) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1093473403841432088521736192, coefficient := (-1093473403841432088521736192) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 1541299552148187573727120064512, coefficient := (-1541299552148187573727120064512) }, { argument := 5238988607787485414855490404352, coefficient := (-5238988607787485414855490404352) }, { argument := 1541299526645563891823664955392, coefficient := (-1541299526645563891823664955392) }, { argument := 227674581756383883214064713728, coefficient := (-227674581756383883214064713728) }, { argument := 227674581756383883214064713728, coefficient := (-227674581756383883214064713728) }, { argument := 11143001195596493883038498816, coefficient := (-11143001195596493883038498816) }, { argument := 1463019881857589207307701452800, coefficient := (-1463019881857589207307701452800) }, { argument := 33939560846057955250963218432, coefficient := (-33939560846057955250963218432) }, { argument := 14964481917769115903828946845696, coefficient := (-14964481917769115903828946845696) }, { argument := 18709260168237858161495638016, coefficient := (-18709260168237858161495638016) }, { argument := 1296010174033096581905907712, coefficient := (-1296010174033096581905907712) }, { argument := 33939560846057955250963218432, coefficient := (-33939560846057955250963218432) }, { argument := 33241406185230506902570401792, coefficient := (-33241406185230506902570401792) }, { argument := 18709260168237858161495638016, coefficient := (-18709260168237858161495638016) }, { argument := 424790750720117730035342770176, coefficient := (-424790750720117730035342770176) }, { argument := 32981432045118028505646366720, coefficient := (-32981432045118028505646366720) }, { argument := 1463020051997280904636488744960, coefficient := (-1463020051997280904636488744960) }, { argument := 33939560846057955250963218432, coefficient := (-33939560846057955250963218432) }, { argument := 1296010174033096581905907712, coefficient := (-1296010174033096581905907712) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
