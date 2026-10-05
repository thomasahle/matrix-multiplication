import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

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
def constantNumerator : ℤ := (-40089817561682203035157196563283968)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14357155, 1508202635, 10433, 15603717819, 10615, 171,
    10433, 6011, 10615, 166463, 1653, 754101703,
    10433, 171, 1653, 171, 2625, 6011,
    14361225, 4518958475053315, 2714643, 80822671167420551, 133688619, 1070089,
    323288520832392459, 1098761, 1098761, 37662467, 1012745, 133688619,
    37662467, 9040106271993555, 1070089, 1012745, 2714643, 23991250929102687,
    857295105, 279748929, 328178180625521297, 2824561767, 95965002617829363, 5658147693,
    2535788679, 857295105, 279748929, 509, 9671, 14761,
    152191, 4581, 14761, 4581, 4581, 392439,
    4581, 152191, 392439, 509, 4581, 4581,
    9671, 857295105, 3066916635, 214323705
  ]
def negativeCoefficients : Array ℕ := #[
    67799747561364341128041594880, 7122285572899681272811445288960, 201803569216630818875352547328, 73686474036601441275156338049024, 205323961203348619032096931840, 6615242084931250843992195072,
    201803569216630818875352547328, 116269649627256575506541182976, 205323961203348619032096931840, 3219862699368160260945826807808, 127894680308670849650515771392, 7122289213844239565307905048576,
    201803569216630818875352547328, 6615242084931250843992195072, 127894680308670849650515771392, 6615242084931250843992195072, 203099537695257701350637568000, 116269649627256575506541182976,
    67818967592949620584061337600, 5087894926088213569571714498560, 25639078232313404583686701056, 181996475876341662206289560731648, 631326653506730025638978125824, 20213409709149983108314955776,
    181995257744240188960541358686208, 20755008476337336978583322624, 20755008476337336978583322624, 355711943645968156325067096064, 19130212174775275367778222080, 631326653506730025638978125824,
    355711943645968156325067096064, 5089127404742482257219063644160, 20213409709149983108314955776, 19130212174775275367778222080, 25639078232313404583686701056, 54023494372229463561063289061376,
    15814303397578957792141639680, 645057112269668015205777408, 184747891497028130382348669681664, 13025992009058457339316666368, 54023493753783124045792863584256, 13046800303002640178516852736,
    11694261196630755630504738816, 15814303397578957792141639680, 645057112269668015205777408, 153835810545961562481360896, 182680025023329355446616064, 139413703307277665998733312,
    1437403354788828349435215872, 173065286864206757791531008, 139413703307277665998733312, 173065286864206757791531008, 173065286864206757791531008, 7412963120683522792070578176,
    173065286864206757791531008, 1437403354788828349435215872, 7412963120683522792070578176, 153835810545961562481360896, 173065286864206757791531008, 173065286864206757791531008,
    182680025023329355446616064, 15814303397578957792141639680, 56574626261247490009501532160, 15814298140256896784919429120
  ]
def negativeScales : Array ℕ := #[
    23, 30, 13, 33, 13, 7,
    13, 12, 13, 17, 10, 29,
    13, 7, 10, 7, 11, 12,
    23, 52, 21, 56, 26, 20,
    58, 20, 20, 25, 19, 26,
    25, 53, 20, 19, 21, 54,
    29, 28, 58, 31, 56, 32,
    31, 29, 28, 8, 13, 13,
    17, 12, 13, 12, 12, 18,
    12, 17, 18, 8, 12, 12,
    13, 29, 31, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23775266559021653, 30490183129323792, 13348866442756552, 33861170764716760, 13373816750792743, 7417852514885912,
    13348866442756552, 12553389304723092, 13373816750792743, 17344842017207997, 10690871009350625, 29490183866835826,
    13348866442756552, 7417852514885912, 10690871009350625, 7417852514885912, 11358101707440849, 12553389304723092,
    23775675479643487, 52004911723379785, 21372331052438730, 56165609551187975, 26994301433794333, 20029299360828112,
    58165599894962409, 20067446177983877, 20067446177983877, 25166624167936826, 19949839542065510, 26994301433794333,
    25166624167936826, 53005261155815601, 20029299360828112, 19949839542065510, 21372331052438730, 54413357901429924,
    29675216665034029, 28059557367050000, 58187256935575467, 31395379903595749, 56413357884914342, 32397682689465170,
    31239787376884051, 29675216665034029, 28059557367050000, 8991521866745102, 13239449359519281, 13849502842919026,
    17215523520273801, 12161446847518008, 13849502842919026, 12161446847518008, 12161446847518008, 18582108895994150,
    12161446847518008, 17215523520273801, 18582108895994150, 8991521866745102, 12161446847518008, 12161446847518008,
    13239449359519281, 29675216665034029, 31514141805754109, 27675216185423038
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
noncomputable def negativeCeiling : ℝ := 24762123329 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 67799747561364341128041594880, coefficient := (-67799747561364341128041594880) }, { argument := 7122285572899681272811445288960, coefficient := (-7122285572899681272811445288960) }, { argument := 201803569216630818875352547328, coefficient := (-201803569216630818875352547328) }, { argument := 73686474036601441275156338049024, coefficient := (-73686474036601441275156338049024) }, { argument := 205323961203348619032096931840, coefficient := (-205323961203348619032096931840) }, { argument := 6615242084931250843992195072, coefficient := (-6615242084931250843992195072) }, { argument := 201803569216630818875352547328, coefficient := (-201803569216630818875352547328) }, { argument := 116269649627256575506541182976, coefficient := (-116269649627256575506541182976) }, { argument := 205323961203348619032096931840, coefficient := (-205323961203348619032096931840) }, { argument := 3219862699368160260945826807808, coefficient := (-3219862699368160260945826807808) }, { argument := 127894680308670849650515771392, coefficient := (-127894680308670849650515771392) }, { argument := 7122289213844239565307905048576, coefficient := (-7122289213844239565307905048576) }, { argument := 201803569216630818875352547328, coefficient := (-201803569216630818875352547328) }, { argument := 6615242084931250843992195072, coefficient := (-6615242084931250843992195072) }, { argument := 127894680308670849650515771392, coefficient := (-127894680308670849650515771392) }, { argument := 6615242084931250843992195072, coefficient := (-6615242084931250843992195072) }, { argument := 203099537695257701350637568000, coefficient := (-203099537695257701350637568000) }, { argument := 116269649627256575506541182976, coefficient := (-116269649627256575506541182976) }, { argument := 67818967592949620584061337600, coefficient := (-67818967592949620584061337600) }, { argument := 5087894926088213569571714498560, coefficient := (-5087894926088213569571714498560) }, { argument := 25639078232313404583686701056, coefficient := (-25639078232313404583686701056) }, { argument := 181996475876341662206289560731648, coefficient := (-181996475876341662206289560731648) }, { argument := 631326653506730025638978125824, coefficient := (-631326653506730025638978125824) }, { argument := 20213409709149983108314955776, coefficient := (-20213409709149983108314955776) }, { argument := 181995257744240188960541358686208, coefficient := (-181995257744240188960541358686208) }, { argument := 20755008476337336978583322624, coefficient := (-20755008476337336978583322624) }, { argument := 20755008476337336978583322624, coefficient := (-20755008476337336978583322624) }, { argument := 355711943645968156325067096064, coefficient := (-355711943645968156325067096064) }, { argument := 19130212174775275367778222080, coefficient := (-19130212174775275367778222080) }, { argument := 631326653506730025638978125824, coefficient := (-631326653506730025638978125824) }, { argument := 355711943645968156325067096064, coefficient := (-355711943645968156325067096064) }, { argument := 5089127404742482257219063644160, coefficient := (-5089127404742482257219063644160) }, { argument := 20213409709149983108314955776, coefficient := (-20213409709149983108314955776) }, { argument := 19130212174775275367778222080, coefficient := (-19130212174775275367778222080) }, { argument := 25639078232313404583686701056, coefficient := (-25639078232313404583686701056) }, { argument := 54023494372229463561063289061376, coefficient := (-54023494372229463561063289061376) }, { argument := 15814303397578957792141639680, coefficient := (-15814303397578957792141639680) }, { argument := 645057112269668015205777408, coefficient := (-645057112269668015205777408) }, { argument := 184747891497028130382348669681664, coefficient := (-184747891497028130382348669681664) }, { argument := 13025992009058457339316666368, coefficient := (-13025992009058457339316666368) }, { argument := 54023493753783124045792863584256, coefficient := (-54023493753783124045792863584256) }, { argument := 13046800303002640178516852736, coefficient := (-13046800303002640178516852736) }, { argument := 11694261196630755630504738816, coefficient := (-11694261196630755630504738816) }, { argument := 15814303397578957792141639680, coefficient := (-15814303397578957792141639680) }, { argument := 645057112269668015205777408, coefficient := (-645057112269668015205777408) }, { argument := 153835810545961562481360896, coefficient := (-153835810545961562481360896) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 139413703307277665998733312, coefficient := (-139413703307277665998733312) }, { argument := 1437403354788828349435215872, coefficient := (-1437403354788828349435215872) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 139413703307277665998733312, coefficient := (-139413703307277665998733312) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 7412963120683522792070578176, coefficient := (-7412963120683522792070578176) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 1437403354788828349435215872, coefficient := (-1437403354788828349435215872) }, { argument := 7412963120683522792070578176, coefficient := (-7412963120683522792070578176) }, { argument := 153835810545961562481360896, coefficient := (-153835810545961562481360896) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 15814303397578957792141639680, coefficient := (-15814303397578957792141639680) }, { argument := 56574626261247490009501532160, coefficient := (-56574626261247490009501532160) }, { argument := 15814298140256896784919429120, coefficient := (-15814298140256896784919429120) }] }

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
def constantNumerator : ℤ := (-101898880635980310289615248450125824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4523400596242983, 509, 4523392963755481, 257, 279748929, 1000783323,
    69937209, 2666515, 9671, 2666515, 4883, 14064251,
    4518950844430077, 2714643, 80822530956625785, 133688619, 1070089, 323287959989314293,
    1098761, 1098761, 37662467, 1012745, 133688619, 37662467,
    9040091010634029, 1070089, 1012745, 2714643, 656356836804206267, 3066916635,
    1000783323, 1122264688263845427, 10104683229, 656356828799767775, 20241649791, 9071616573,
    3066916635, 1000783323, 80908045973216243, 14761, 80907905729799181, 7453,
    2824561767, 10104683229, 706140207, 131306795, 152191, 131306795,
    76843, 1478630847, 1051145, 4581, 1051145, 2313,
    1285, 191930005232682573, 214323705, 69937209, 82044544154472399, 706140207,
    191930003035519803, 1414536453, 633946959, 214323705
  ]
def negativeCoefficients : Array ℕ := #[
    5092896309921844416868245307392, 153835810545961562481360896, 5092887716504876937576284422144, 155346967820479848949743616, 645057112269668015205777408, 2307649229077200250387562496,
    645056897826268158332239872, 25184522124138304013997178880, 182680025023329355446616064, 25184522124138304013997178880, 184474524286819820627820544, 66416547529065890566369181696,
    5087886334770220754209811202048, 25639078232313404583686701056, 181996160149700131466944110919680, 631326653506730025638978125824, 20213409709149983108314955776, 181994942017655458745596212412416,
    20755008476337336978583322624, 20755008476337336978583322624, 355711943645968156325067096064, 19130212174775275367778222080, 631326653506730025638978125824, 355711943645968156325067096064,
    5089118813360847949622881026048, 20213409709149983108314955776, 19130212174775275367778222080, 25639078232313404583686701056, 184748025353343799918804600881152, 56574626261247490009501532160,
    2307649229077200250387562496, 631778853984515015070732175540224, 46599626367817011507826262016, 184748023100294661801226167910400, 46674066665529179257838764032, 41835447314238275507026132992,
    56574626261247490009501532160, 2307649229077200250387562496, 182188722848125815683017043083264, 139413703307277665998733312, 182188407048025404888886582181888, 140783189587309863110705152,
    13025992009058457339316666368, 46599626367817011507826262016, 13025987678685286035999424512, 620078807681035515797511864320, 1437403354788828349435215872, 620078807681035515797511864320,
    1451523230572608588624166912, 6982636752409954492916812480512, 19855567666544052872601927680, 173065286864206757791531008, 19855567666544052872601927680, 174765338798039830068461568,
    198844118810214206655671828480, 54023493752945411449430514597888, 15814298140256896784919429120, 645056897826268158332239872, 184747889240932050974625289469952, 13025987678685286035999424512,
    54023493134499071934160089120768, 13046795965711939847558529024, 11694257308979442096216735744, 15814298140256896784919429120
  ]
def negativeScales : Array ℕ := #[
    52, 8, 52, 8, 28, 29,
    26, 21, 13, 21, 12, 23,
    52, 21, 56, 26, 20, 58,
    20, 20, 25, 19, 26, 25,
    53, 20, 19, 21, 59, 31,
    29, 59, 33, 59, 34, 33,
    31, 29, 56, 13, 56, 12,
    31, 33, 29, 26, 17, 26,
    16, 30, 20, 12, 20, 11,
    10, 57, 27, 26, 56, 29,
    57, 30, 29, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    52006329191249922, 8991521866745102, 52006326756939512, 8005624549193879, 28059557367050000, 29898482512059889,
    26059556887439009, 21346524012989090, 13239449359519281, 21346524012989090, 12253552062637464, 23745529387536677,
    52004909287271629, 21372331052438730, 56165607048405144, 26994301433794333, 20029299360828112, 58165597392163277,
    20067446177983877, 20067446177983877, 25166624167936826, 19949839542065510, 26994301433794333, 25166624167936826,
    53005258720279378, 20029299360828112, 19949839542065510, 21372331052438730, 59187257980858157, 31514141805754109,
    29898482512059889, 59961118698985689, 33234305044355348, 59187257963264124, 34236607830224769, 33078712517643656,
    31514141805754109, 29898482512059889, 56167132698089896, 13849502842919026, 56167130197366325, 12863605546562187,
    31395379903595749, 33234305044355348, 29395379423984758, 26968366349505954, 17215523520273801, 26968366349505954,
    16229626223391984, 30461614770062324, 20003530264648884, 12161446847518008, 20003530264648884, 11175549550636191,
    10327552644081241, 57413357884891971, 27675216185423038, 26059556887439009, 56187256917957628, 29395379423984758,
    57413357868376388, 30397682209854179, 29239786897273060, 27675216185423038
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
noncomputable def negativeCeiling : ℝ := 358082118073 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5092896309921844416868245307392, coefficient := (-5092896309921844416868245307392) }, { argument := 153835810545961562481360896, coefficient := (-153835810545961562481360896) }, { argument := 5092887716504876937576284422144, coefficient := (-5092887716504876937576284422144) }, { argument := 155346967820479848949743616, coefficient := (-155346967820479848949743616) }, { argument := 645057112269668015205777408, coefficient := (-645057112269668015205777408) }, { argument := 2307649229077200250387562496, coefficient := (-2307649229077200250387562496) }, { argument := 645056897826268158332239872, coefficient := (-645056897826268158332239872) }, { argument := 25184522124138304013997178880, coefficient := (-25184522124138304013997178880) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 25184522124138304013997178880, coefficient := (-25184522124138304013997178880) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 66416547529065890566369181696, coefficient := (-66416547529065890566369181696) }, { argument := 5087886334770220754209811202048, coefficient := (-5087886334770220754209811202048) }, { argument := 25639078232313404583686701056, coefficient := (-25639078232313404583686701056) }, { argument := 181996160149700131466944110919680, coefficient := (-181996160149700131466944110919680) }, { argument := 631326653506730025638978125824, coefficient := (-631326653506730025638978125824) }, { argument := 20213409709149983108314955776, coefficient := (-20213409709149983108314955776) }, { argument := 181994942017655458745596212412416, coefficient := (-181994942017655458745596212412416) }, { argument := 20755008476337336978583322624, coefficient := (-20755008476337336978583322624) }, { argument := 20755008476337336978583322624, coefficient := (-20755008476337336978583322624) }, { argument := 355711943645968156325067096064, coefficient := (-355711943645968156325067096064) }, { argument := 19130212174775275367778222080, coefficient := (-19130212174775275367778222080) }, { argument := 631326653506730025638978125824, coefficient := (-631326653506730025638978125824) }, { argument := 355711943645968156325067096064, coefficient := (-355711943645968156325067096064) }, { argument := 5089118813360847949622881026048, coefficient := (-5089118813360847949622881026048) }, { argument := 20213409709149983108314955776, coefficient := (-20213409709149983108314955776) }, { argument := 19130212174775275367778222080, coefficient := (-19130212174775275367778222080) }, { argument := 25639078232313404583686701056, coefficient := (-25639078232313404583686701056) }, { argument := 184748025353343799918804600881152, coefficient := (-184748025353343799918804600881152) }, { argument := 56574626261247490009501532160, coefficient := (-56574626261247490009501532160) }, { argument := 2307649229077200250387562496, coefficient := (-2307649229077200250387562496) }, { argument := 631778853984515015070732175540224, coefficient := (-631778853984515015070732175540224) }, { argument := 46599626367817011507826262016, coefficient := (-46599626367817011507826262016) }, { argument := 184748023100294661801226167910400, coefficient := (-184748023100294661801226167910400) }, { argument := 46674066665529179257838764032, coefficient := (-46674066665529179257838764032) }, { argument := 41835447314238275507026132992, coefficient := (-41835447314238275507026132992) }, { argument := 56574626261247490009501532160, coefficient := (-56574626261247490009501532160) }, { argument := 2307649229077200250387562496, coefficient := (-2307649229077200250387562496) }, { argument := 182188722848125815683017043083264, coefficient := (-182188722848125815683017043083264) }, { argument := 139413703307277665998733312, coefficient := (-139413703307277665998733312) }, { argument := 182188407048025404888886582181888, coefficient := (-182188407048025404888886582181888) }, { argument := 140783189587309863110705152, coefficient := (-140783189587309863110705152) }, { argument := 13025992009058457339316666368, coefficient := (-13025992009058457339316666368) }, { argument := 46599626367817011507826262016, coefficient := (-46599626367817011507826262016) }, { argument := 13025987678685286035999424512, coefficient := (-13025987678685286035999424512) }, { argument := 620078807681035515797511864320, coefficient := (-620078807681035515797511864320) }, { argument := 1437403354788828349435215872, coefficient := (-1437403354788828349435215872) }, { argument := 620078807681035515797511864320, coefficient := (-620078807681035515797511864320) }, { argument := 1451523230572608588624166912, coefficient := (-1451523230572608588624166912) }, { argument := 6982636752409954492916812480512, coefficient := (-6982636752409954492916812480512) }, { argument := 19855567666544052872601927680, coefficient := (-19855567666544052872601927680) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 19855567666544052872601927680, coefficient := (-19855567666544052872601927680) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 198844118810214206655671828480, coefficient := (-198844118810214206655671828480) }, { argument := 54023493752945411449430514597888, coefficient := (-54023493752945411449430514597888) }, { argument := 15814298140256896784919429120, coefficient := (-15814298140256896784919429120) }, { argument := 645056897826268158332239872, coefficient := (-645056897826268158332239872) }, { argument := 184747889240932050974625289469952, coefficient := (-184747889240932050974625289469952) }, { argument := 13025987678685286035999424512, coefficient := (-13025987678685286035999424512) }, { argument := 54023493134499071934160089120768, coefficient := (-54023493134499071934160089120768) }, { argument := 13046795965711939847558529024, coefficient := (-13046795965711939847558529024) }, { argument := 11694257308979442096216735744, coefficient := (-11694257308979442096216735744) }, { argument := 15814298140256896784919429120, coefficient := (-15814298140256896784919429120) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
