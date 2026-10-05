import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-491171401185941054235936503048962048)
def positiveArguments : Array ℕ := #[
    273305, 151105, 6417841723, 8695, 8225, 11045,
    320653393, 31764387647, 424575, 318171151805, 435675, 13875,
    424575, 241425, 435675, 6801525, 8325, 15882200749,
    424575, 13875, 8325, 13875, 213675, 241425,
    320652633, 221803027, 9259412973, 13755, 12183, 570243,
    155235, 4629707661, 570243, 13755, 13755, 5895,
    13755, 155235, 5895, 110900339, 12183, 5023777,
    3507, 32915423, 5649, 175, 5649, 3773,
    5052449, 3507, 21
  ]
def positiveCoefficients : Array ℕ := #[
    10572975076152839250978285813760, 5845591551131793326207255183360, 60614801290115147645330879676416, 336371520049574421570246410240, 318189275722570398782665523200, 427282741684594535508150845440,
    1514242835721628114477832470528, 150003079573071395537197897613312, 8212474877806098909613994803200, 1502520783099961819313361681121280, 8427180103369657051041811660800, 268381531954447676784771072000,
    8212474877806098909613994803200, 4669838656007389576055016652800, 8427180103369657051041811660800, 131560626964070251159894779494400, 5152925413525395394267604582400, 150003144982569549764653752516608,
    8212474877806098909613994803200, 268381531954447676784771072000, 5152925413525395394267604582400, 268381531954447676784771072000, 8266151184196988444970949017600, 4669838656007389576055016652800,
    1514239246723101133547470061568, 1047435180503830954813834657792, 43726341474743575159604099678208, 532120788761575177538670428160, 471306984331680871534250950656, 22060207556944159503103165464576,
    6005363187452062717936423403520, 43726352567582443420400706650112, 22060207556944159503103165464576, 532120788761575177538670428160, 532120788761575177538670428160, 456103533224207295033146081280,
    532120788761575177538670428160, 6005363187452062717936423403520, 456103533224207295033146081280, 1047424087664962694017227685888, 471306984331680871534250950656, 47448232244422835245452099584,
    135670491180432144502225895424, 621754761378706504274916933632, 218535102560097286653286023168, 6769984589841923378354585600, 218535102560097286653286023168, 145960867756991868037324865536,
    47719031628016512180586283008, 135670491180432144502225895424, 6499185206248246443220402176
  ]
def positiveScales : Array ℕ := #[
    18, 17, 32, 13, 13, 13,
    28, 34, 18, 38, 18, 13,
    18, 17, 18, 22, 13, 33,
    18, 13, 13, 13, 17, 17,
    28, 27, 33, 13, 13, 19,
    17, 32, 19, 13, 13, 12,
    13, 17, 12, 26, 13, 22,
    11, 24, 12, 7, 12, 11,
    22, 11, 4
  ]
def negativeArguments : Array ℕ := #[
    14255, 3167, 1889, 5
  ]
def negativeCoefficients : Array ℕ := #[
    4517589826563352529583876048158720, 2007324725461401257270029525712896, 149661998989445333714204522184704, 1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    13, 11, 10, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    18060152328038218, 17205191873892946, 32579441064257280, 13085970312193949, 13005799963509966, 13431105798242635,
    28256439432260493, 34886691155832379, 18695659898813424, 38211012077938472, 18732892805006900, 13760200150994793,
    18695659898813424, 17881215551781447, 18732892805006900, 22697426824987439, 13023234556845986, 33886691784925715,
    18695659898813424, 13760200150994793, 13023234556845986, 13760200150994793, 17705058596814672, 17881215551781447,
    28256436012837669, 27724703813535973, 33108273586587641, 13747668519190317, 13572581812645319, 19121217306325350,
    17244094345323071, 32108273952581709, 19121217306325350, 13747668519190317, 13747668519190317, 12525276097867086,
    13747668519190317, 17244094345323071, 12525276097867086, 26724688534625485, 13572581812645319, 22260340995310394,
    11776021715228447, 24972260401399903, 12463779785335379, 7451211111832325, 12463779785335379, 11881496384617007,
    22268551423273383, 11776021715228447, 4392317422778759
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13799180419460638, 11628901152040529, 10883406989622233, 2321928094887363
  ]

abbrev PositiveTerm := Fin 51
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
noncomputable def positiveFloor : ℝ := 117899057881 / 125000000000
noncomputable def negativeCeiling : ℝ := 525505209671 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10572975076152839250978285813760, coefficient := 10572975076152839250978285813760 }, { argument := 5845591551131793326207255183360, coefficient := 5845591551131793326207255183360 }, { argument := 60614801290115147645330879676416, coefficient := 60614801290115147645330879676416 }, { argument := 336371520049574421570246410240, coefficient := 336371520049574421570246410240 }, { argument := 318189275722570398782665523200, coefficient := 318189275722570398782665523200 }, { argument := 427282741684594535508150845440, coefficient := 427282741684594535508150845440 }, { argument := 4517589826563352529583876048158720, coefficient := (-4517589826563352529583876048158720) }, { argument := 1514242835721628114477832470528, coefficient := 1514242835721628114477832470528 }, { argument := 150003079573071395537197897613312, coefficient := 150003079573071395537197897613312 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 1502520783099961819313361681121280, coefficient := 1502520783099961819313361681121280 }, { argument := 8427180103369657051041811660800, coefficient := 8427180103369657051041811660800 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 4669838656007389576055016652800, coefficient := 4669838656007389576055016652800 }, { argument := 8427180103369657051041811660800, coefficient := 8427180103369657051041811660800 }, { argument := 131560626964070251159894779494400, coefficient := 131560626964070251159894779494400 }, { argument := 5152925413525395394267604582400, coefficient := 5152925413525395394267604582400 }, { argument := 150003144982569549764653752516608, coefficient := 150003144982569549764653752516608 }, { argument := 8212474877806098909613994803200, coefficient := 8212474877806098909613994803200 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 5152925413525395394267604582400, coefficient := 5152925413525395394267604582400 }, { argument := 268381531954447676784771072000, coefficient := 268381531954447676784771072000 }, { argument := 8266151184196988444970949017600, coefficient := 8266151184196988444970949017600 }, { argument := 4669838656007389576055016652800, coefficient := 4669838656007389576055016652800 }, { argument := 1514239246723101133547470061568, coefficient := 1514239246723101133547470061568 }, { argument := 2007324725461401257270029525712896, coefficient := (-2007324725461401257270029525712896) }, { argument := 1047435180503830954813834657792, coefficient := 1047435180503830954813834657792 }, { argument := 43726341474743575159604099678208, coefficient := 43726341474743575159604099678208 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 471306984331680871534250950656, coefficient := 471306984331680871534250950656 }, { argument := 22060207556944159503103165464576, coefficient := 22060207556944159503103165464576 }, { argument := 6005363187452062717936423403520, coefficient := 6005363187452062717936423403520 }, { argument := 43726352567582443420400706650112, coefficient := 43726352567582443420400706650112 }, { argument := 22060207556944159503103165464576, coefficient := 22060207556944159503103165464576 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 456103533224207295033146081280, coefficient := 456103533224207295033146081280 }, { argument := 532120788761575177538670428160, coefficient := 532120788761575177538670428160 }, { argument := 6005363187452062717936423403520, coefficient := 6005363187452062717936423403520 }, { argument := 456103533224207295033146081280, coefficient := 456103533224207295033146081280 }, { argument := 1047424087664962694017227685888, coefficient := 1047424087664962694017227685888 }, { argument := 471306984331680871534250950656, coefficient := 471306984331680871534250950656 }, { argument := 149661998989445333714204522184704, coefficient := (-149661998989445333714204522184704) }, { argument := 47448232244422835245452099584, coefficient := 47448232244422835245452099584 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 621754761378706504274916933632, coefficient := 621754761378706504274916933632 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 6769984589841923378354585600, coefficient := 6769984589841923378354585600 }, { argument := 218535102560097286653286023168, coefficient := 218535102560097286653286023168 }, { argument := 145960867756991868037324865536, coefficient := 145960867756991868037324865536 }, { argument := 47719031628016512180586283008, coefficient := 47719031628016512180586283008 }, { argument := 135670491180432144502225895424, coefficient := 135670491180432144502225895424 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }] }

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

end TermShard10


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
