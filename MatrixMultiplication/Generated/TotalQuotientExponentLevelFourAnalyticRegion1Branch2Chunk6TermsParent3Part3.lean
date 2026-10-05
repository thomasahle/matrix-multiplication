import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

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
def constantNumerator : ℤ := 5224773322607300481584263031947264
def positiveArguments : Array ℕ := #[
    9, 9, 3, 3, 3, 3,
    837, 10017, 14985, 4347, 837, 17361,
    8721, 837, 10017, 837, 135, 105,
    15, 141, 1665, 117, 105, 1665,
    15, 117, 117, 117, 117, 117,
    135, 141, 3474135, 5963049, 3474135, 2819499,
    104135253, 208262199, 5647305, 282707, 155538595, 3232081991,
    77769311, 2261599, 52129619, 3803812013, 105
  ]
def positiveCoefficients : Array ℕ := #[
    45635421608216258453881315393536, 1426106925256758076683791106048, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016, 475368975085586025561263702016,
    32379869152558227815330217984, 775027835845103388354032959488, 579704109021606981855105515520, 672665668846693506873311625216, 32379869152558227815330217984, 671621156938546467266365489152,
    674754692662987586087203897344, 32379869152558227815330217984, 775027835845103388354032959488, 32379869152558227815330217984, 41780476325881584277845442560, 32495926031241232216102010880,
    37138201178561408246973726720, 43637386384809654690194128896, 515292541352539539426760458240, 1158711876771115937305580273664, 32495926031241232216102010880, 515292541352539539426760458240,
    37138201178561408246973726720, 36209746149097373040799383552, 36209746149097373040799383552, 36209746149097373040799383552, 1158711876771115937305580273664, 36209746149097373040799383552,
    41780476325881584277845442560, 43637386384809654690194128896, 262498218895429357991740047360, 901110487465899360700311011328, 262498218895429357991740047360, 53258830304337927241482633216,
    1967059313809402681393888100352, 1966980856412656285108307755008, 53337287701084323527062978560, 10680368490181030315426840576, 1469020495641272369373501194240, 15263075664184990295746188148736,
    1469020750649062444334342733824, 10680099315291506745649659904, 246175165530364631655146061824, 17962994357328115176904796930048, 32495926031241232216102010880
  ]
def positiveScales : Array ℕ := #[
    3, 3, 1, 1, 1, 1,
    9, 13, 13, 12, 9, 14,
    13, 9, 13, 9, 7, 6,
    3, 7, 10, 6, 6, 10,
    3, 6, 6, 6, 6, 6,
    7, 7, 21, 22, 21, 21,
    26, 27, 22, 18, 27, 31,
    26, 21, 25, 31, 6
  ]
def negativeArguments : Array ℕ := #[
    21544253403, 1035522687, 16564059, 359101695, 13261900545, 26522747991,
    719256489, 3474135, 5963049, 3474135, 9, 3,
    27, 3, 9, 51, 115
  ]
def negativeCoefficients : Array ℕ := #[
    24838833049017943139788259328, 2387752748701130118370689024, 19097059824676585114435584, 6624257064100304922995589120, 244638885284604222747936030720, 244629172160735583020387401728,
    6633970187968944650544218112, 131249109447714678995870023680, 450555243732949680350155505664, 131249109447714678995870023680, 1426106925256758076683791106048, 1901475900342344102245054808064,
    4278320775770274230051373318144, 3802951800684688204490109616128, 1426106925256758076683791106048, 4040636288227481217270741467136, 18222477378280797646515108577280
  ]
def negativeScales : Array ℕ := #[
    34, 29, 23, 28, 33, 34,
    29, 21, 22, 21, 3, 1,
    4, 1, 3, 5, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 3169925001442312, 1584962500720924, 1584962500720924, 1584962500720924, 1584962500720924,
    9709083812544787, 13290162878784271, 13871231463241128, 12085804380278085, 9709083812544787, 14083562429491415,
    13090277856857393, 9709083812544787, 13290162878784271, 9709083812544787, 7076815597050830, 6714245517659862,
    3906890595303263, 7139551352398793, 10701306461953989, 6870364719426147, 6714245517659862, 10701306461953989,
    3906890595303263, 6870364719426147, 6870364719426147, 6870364719426147, 6870364719426147, 6870364719426147,
    7076815597050830, 7139551352398793, 21728222385553381, 22507618761153576, 21728222385553381, 21427007400590655,
    26633883307260598, 27633825763314771, 22429131119911108, 18108948080068786, 27212697371006384, 31589816650624196,
    26212697621444307, 21108911719696738, 25635599979950815, 31824798802901772, 6714245517659862
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34326584052870660, 29947712025553707, 23981552928407170, 28419817221798848, 33626568489823481, 34626511208031099,
    29421931090851994, 21728222385700655, 22507618761153948, 21728222385700655, 3169925001442313, 1584962500724866,
    4754887502413606, 1584962500724866, 3169925001442313, 5672425342008812, 6845490052533228
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 3655491017 / 200000000000
noncomputable def negativeCeiling : ℝ := 2647397097 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24838833049017943139788259328, coefficient := (-24838833049017943139788259328) }, { argument := 2387752748701130118370689024, coefficient := (-2387752748701130118370689024) }, { argument := 19097059824676585114435584, coefficient := (-19097059824676585114435584) }, { argument := 6624257064100304922995589120, coefficient := (-6624257064100304922995589120) }, { argument := 244638885284604222747936030720, coefficient := (-244638885284604222747936030720) }, { argument := 244629172160735583020387401728, coefficient := (-244629172160735583020387401728) }, { argument := 6633970187968944650544218112, coefficient := (-6633970187968944650544218112) }, { argument := 131249109447714678995870023680, coefficient := (-131249109447714678995870023680) }, { argument := 450555243732949680350155505664, coefficient := (-450555243732949680350155505664) }, { argument := 131249109447714678995870023680, coefficient := (-131249109447714678995870023680) }, { argument := 45635421608216258453881315393536, coefficient := 45635421608216258453881315393536 }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 579704109021606981855105515520, coefficient := 579704109021606981855105515520 }, { argument := 672665668846693506873311625216, coefficient := 672665668846693506873311625216 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 671621156938546467266365489152, coefficient := 671621156938546467266365489152 }, { argument := 674754692662987586087203897344, coefficient := 674754692662987586087203897344 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 775027835845103388354032959488, coefficient := 775027835845103388354032959488 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 43637386384809654690194128896, coefficient := 43637386384809654690194128896 }, { argument := 515292541352539539426760458240, coefficient := 515292541352539539426760458240 }, { argument := 1158711876771115937305580273664, coefficient := 1158711876771115937305580273664 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 515292541352539539426760458240, coefficient := 515292541352539539426760458240 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 1158711876771115937305580273664, coefficient := 1158711876771115937305580273664 }, { argument := 36209746149097373040799383552, coefficient := 36209746149097373040799383552 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 43637386384809654690194128896, coefficient := 43637386384809654690194128896 }, { argument := 3802951800684688204490109616128, coefficient := (-3802951800684688204490109616128) }, { argument := 262498218895429357991740047360, coefficient := 262498218895429357991740047360 }, { argument := 901110487465899360700311011328, coefficient := 901110487465899360700311011328 }, { argument := 262498218895429357991740047360, coefficient := 262498218895429357991740047360 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 53258830304337927241482633216, coefficient := 53258830304337927241482633216 }, { argument := 1967059313809402681393888100352, coefficient := 1967059313809402681393888100352 }, { argument := 1966980856412656285108307755008, coefficient := 1966980856412656285108307755008 }, { argument := 53337287701084323527062978560, coefficient := 53337287701084323527062978560 }, { argument := 4040636288227481217270741467136, coefficient := (-4040636288227481217270741467136) }, { argument := 10680368490181030315426840576, coefficient := 10680368490181030315426840576 }, { argument := 1469020495641272369373501194240, coefficient := 1469020495641272369373501194240 }, { argument := 15263075664184990295746188148736, coefficient := 15263075664184990295746188148736 }, { argument := 1469020750649062444334342733824, coefficient := 1469020750649062444334342733824 }, { argument := 10680099315291506745649659904, coefficient := 10680099315291506745649659904 }, { argument := 18222477378280797646515108577280, coefficient := (-18222477378280797646515108577280) }, { argument := 246175165530364631655146061824, coefficient := 246175165530364631655146061824 }, { argument := 17962994357328115176904796930048, coefficient := 17962994357328115176904796930048 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }] }

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
def constantNumerator : ℤ := (-2601908924804000189850287274459136)
def positiveArguments : Array ℕ := #[
    93, 4353, 1185, 1901906121, 4353, 105,
    105, 45, 105, 1185, 45, 26064695,
    93, 176680221, 28557, 925575907, 45999, 1425,
    45999, 30723, 176913693, 28557, 171, 14445,
    13203, 14445, 13203
  ]
def positiveCoefficients : Array ℕ := #[
    28782105913385091391404638208, 1347188247752315084158971936768, 366739736638293906438865551360, 17962995438750039754053550866432, 1347188247752315084158971936768, 32495926031241232216102010880,
    32495926031241232216102010880, 27853650883921056185230295040, 32495926031241232216102010880, 366739736638293906438865551360, 27853650883921056185230295040, 246174084108440054506392125440,
    28782105913385091391404638208, 834348753836401630547401506816, 552372714091759445473348288512, 8741817281136943662869768044544, 889750060423253238516950237184, 27563508687213545183300812800,
    889750060423253238516950237184, 594269247296324034151965523968, 835451294183890172354733539328, 552372714091759445473348288512, 26460968339725003375968780288, 558813870858666189716182794240,
    510766323083902367796660535296, 558813870858666189716182794240, 510766323083902367796660535296
  ]
def positiveScales : Array ℕ := #[
    6, 12, 10, 30, 12, 6,
    6, 5, 6, 10, 5, 24,
    6, 27, 14, 29, 15, 10,
    15, 14, 27, 14, 7, 13,
    13, 13, 13
  ]
def negativeArguments : Array ℕ := #[
    253, 11, 27
  ]
def negativeCoefficients : Array ℕ := #[
    40089450232217754822333238870016, 13944156602510523416463735259136, 2139160387885137115025686659072
  ]
def negativeScales : Array ℕ := #[
    7, 3, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6539158811107971, 12087794304787900, 10210671343785621, 30824798889756000, 12087794304787900, 6714245517659862,
    6714245517659862, 5491853096329661, 6714245517659862, 10210671343785621, 5491853096329661, 24635593642327476,
    6539158811107971, 27396565301182111, 14801556807318634, 29785776070247347, 15489314877442509, 10476746203939458,
    15489314877442509, 14907031476611228, 27398470475067745, 14801556807318634, 7417852514885896, 13818282583394157,
    13688578157112273, 13818282583394157, 13688578157112273
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7982993592700323, 3459431618637364, 4754887502413606
  ]

abbrev PositiveTerm := Fin 27
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 2383294787 / 200000000000
noncomputable def negativeCeiling : ℝ := 2277677863 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28782105913385091391404638208, coefficient := 28782105913385091391404638208 }, { argument := 1347188247752315084158971936768, coefficient := 1347188247752315084158971936768 }, { argument := 366739736638293906438865551360, coefficient := 366739736638293906438865551360 }, { argument := 17962995438750039754053550866432, coefficient := 17962995438750039754053550866432 }, { argument := 1347188247752315084158971936768, coefficient := 1347188247752315084158971936768 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 366739736638293906438865551360, coefficient := 366739736638293906438865551360 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 246174084108440054506392125440, coefficient := 246174084108440054506392125440 }, { argument := 28782105913385091391404638208, coefficient := 28782105913385091391404638208 }, { argument := 40089450232217754822333238870016, coefficient := (-40089450232217754822333238870016) }, { argument := 834348753836401630547401506816, coefficient := 834348753836401630547401506816 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 8741817281136943662869768044544, coefficient := 8741817281136943662869768044544 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 594269247296324034151965523968, coefficient := 594269247296324034151965523968 }, { argument := 835451294183890172354733539328, coefficient := 835451294183890172354733539328 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 26460968339725003375968780288, coefficient := 26460968339725003375968780288 }, { argument := 13944156602510523416463735259136, coefficient := (-13944156602510523416463735259136) }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 558813870858666189716182794240, coefficient := 558813870858666189716182794240 }, { argument := 510766323083902367796660535296, coefficient := 510766323083902367796660535296 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
