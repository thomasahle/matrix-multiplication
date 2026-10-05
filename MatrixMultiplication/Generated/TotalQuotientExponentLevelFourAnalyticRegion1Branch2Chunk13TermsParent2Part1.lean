import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-23867943691003379112034413714604032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    69937209, 323630020214958811, 14761, 323629459241391397, 7453, 15292968119,
    1079305, 4581, 1079305, 2313, 5229, 337,
    257, 4883, 7453, 76843, 2313, 7453,
    2313, 2313, 198147, 2313, 76843, 198147,
    257, 2313, 2313, 4883, 5658147693, 20241649791,
    1414536453, 1079305, 4581, 1079305, 2313, 2535788679,
    9071616573, 633946959, 37004035, 392439, 37004035, 198147,
    1285, 994825, 4581, 994825, 2313, 1481,
    857295105, 3066916635, 214323705, 131306795, 152191, 131306795,
    76843, 5229, 37004035, 392439, 37004035, 198147,
    41003, 1629, 9048990422098187, 509
  ]
def negativeCoefficients : Array ℕ := #[
    645056897826268158332239872, 182187504805749323626190609580032, 139413703307277665998733312, 182187189005705677327663433252864, 140783189587309863110705152, 72219000068759643885893870157824,
    20387495027174489709472645120, 173065286864206757791531008, 20387495027174489709472645120, 174765338798039830068461568, 202287139544476670545235017728, 6518528019362080510015700992,
    155346967820479848949743616, 184474524286819820627820544, 140783189587309863110705152, 1451523230572608588624166912, 174765338798039830068461568, 140783189587309863110705152,
    174765338798039830068461568, 174765338798039830068461568, 7485782011849372721265770496, 174765338798039830068461568, 1451523230572608588624166912, 7485782011849372721265770496,
    155346967820479848949743616, 174765338798039830068461568, 174765338798039830068461568, 184474524286819820627820544, 13046800303002640178516852736, 46674066665529179257838764032,
    13046795965711939847558529024, 20387495027174489709472645120, 173065286864206757791531008, 20387495027174489709472645120, 174765338798039830068461568, 11694261196630755630504738816,
    41835447314238275507026132992, 11694257308979442096216735744, 349493229229870503850378526720, 7412963120683522792070578176, 349493229229870503850378526720, 7485782011849372721265770496,
    198844118810214206655671828480, 18791712945283179198860492800, 173065286864206757791531008, 18791712945283179198860492800, 174765338798039830068461568, 114586824886353011695350185984,
    15814303397578957792141639680, 56574626261247490009501532160, 15814298140256896784919429120, 620078807681035515797511864320, 1437403354788828349435215872, 620078807681035515797511864320,
    1451523230572608588624166912, 202287139544476670545235017728, 349493229229870503850378526720, 7412963120683522792070578176, 349493229229870503850378526720, 7485782011849372721265770496,
    3172453464426152963230549409792, 126037770249742779238167085056, 5094128736630072785750242361344, 153835810545961562481360896
  ]
def negativeScales : Array ℕ := #[
    26, 58, 13, 58, 12, 33,
    20, 12, 20, 11, 12, 8,
    8, 12, 12, 16, 11, 12,
    11, 11, 17, 11, 16, 17,
    8, 11, 11, 12, 32, 34,
    30, 20, 12, 20, 11, 31,
    33, 29, 25, 18, 25, 17,
    10, 19, 12, 19, 11, 10,
    29, 31, 27, 26, 17, 26,
    16, 12, 25, 18, 25, 17,
    15, 10, 53, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26059556887439009, 58167123052764198, 13849502842919026, 58167120552024357, 12863605546562187, 33832149387865028,
    20041671181887704, 12161446847518008, 20041671181887704, 11175549550636191, 12352319354846843, 8396604781181865,
    8005624549193879, 12253552062637464, 12863605546562187, 16229626223391984, 11175549550636191, 12863605546562187,
    11175549550636191, 11175549550636191, 17596211599114003, 11175549550636191, 16229626223391984, 17596211599114003,
    8005624549193879, 11175549550636191, 11175549550636191, 12253552062637464, 32397682689465170, 34236607830224769,
    30397682209854179, 20041671181887704, 12161446847518008, 20041671181887704, 11175549550636191, 31239787376884051,
    33078712517643656, 29239786897273060, 25141179258117889, 18582108895994150, 25141179258117889, 17596211599114003,
    10327552644081241, 19924083244126852, 12161446847518008, 19924083244126852, 11175549550636191, 10532355925289620,
    29675216665034029, 31514141805754109, 27675216185423038, 26968366349505954, 17215523520273801, 26968366349505954,
    16229626223391984, 12352319354846843, 25141179258117889, 18582108895994150, 25141179258117889, 17596211599114003,
    15323441848470069, 10669770888560475, 53006678265862141, 8991521866745102
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
noncomputable def negativeCeiling : ℝ := 72358908571 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 645056897826268158332239872, coefficient := (-645056897826268158332239872) }, { argument := 182187504805749323626190609580032, coefficient := (-182187504805749323626190609580032) }, { argument := 139413703307277665998733312, coefficient := (-139413703307277665998733312) }, { argument := 182187189005705677327663433252864, coefficient := (-182187189005705677327663433252864) }, { argument := 140783189587309863110705152, coefficient := (-140783189587309863110705152) }, { argument := 72219000068759643885893870157824, coefficient := (-72219000068759643885893870157824) }, { argument := 20387495027174489709472645120, coefficient := (-20387495027174489709472645120) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 20387495027174489709472645120, coefficient := (-20387495027174489709472645120) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 202287139544476670545235017728, coefficient := (-202287139544476670545235017728) }, { argument := 6518528019362080510015700992, coefficient := (-6518528019362080510015700992) }, { argument := 155346967820479848949743616, coefficient := (-155346967820479848949743616) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 140783189587309863110705152, coefficient := (-140783189587309863110705152) }, { argument := 1451523230572608588624166912, coefficient := (-1451523230572608588624166912) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 140783189587309863110705152, coefficient := (-140783189587309863110705152) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 7485782011849372721265770496, coefficient := (-7485782011849372721265770496) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 1451523230572608588624166912, coefficient := (-1451523230572608588624166912) }, { argument := 7485782011849372721265770496, coefficient := (-7485782011849372721265770496) }, { argument := 155346967820479848949743616, coefficient := (-155346967820479848949743616) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 13046800303002640178516852736, coefficient := (-13046800303002640178516852736) }, { argument := 46674066665529179257838764032, coefficient := (-46674066665529179257838764032) }, { argument := 13046795965711939847558529024, coefficient := (-13046795965711939847558529024) }, { argument := 20387495027174489709472645120, coefficient := (-20387495027174489709472645120) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 20387495027174489709472645120, coefficient := (-20387495027174489709472645120) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 11694261196630755630504738816, coefficient := (-11694261196630755630504738816) }, { argument := 41835447314238275507026132992, coefficient := (-41835447314238275507026132992) }, { argument := 11694257308979442096216735744, coefficient := (-11694257308979442096216735744) }, { argument := 349493229229870503850378526720, coefficient := (-349493229229870503850378526720) }, { argument := 7412963120683522792070578176, coefficient := (-7412963120683522792070578176) }, { argument := 349493229229870503850378526720, coefficient := (-349493229229870503850378526720) }, { argument := 7485782011849372721265770496, coefficient := (-7485782011849372721265770496) }, { argument := 198844118810214206655671828480, coefficient := (-198844118810214206655671828480) }, { argument := 18791712945283179198860492800, coefficient := (-18791712945283179198860492800) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 18791712945283179198860492800, coefficient := (-18791712945283179198860492800) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 114586824886353011695350185984, coefficient := (-114586824886353011695350185984) }, { argument := 15814303397578957792141639680, coefficient := (-15814303397578957792141639680) }, { argument := 56574626261247490009501532160, coefficient := (-56574626261247490009501532160) }, { argument := 15814298140256896784919429120, coefficient := (-15814298140256896784919429120) }, { argument := 620078807681035515797511864320, coefficient := (-620078807681035515797511864320) }, { argument := 1437403354788828349435215872, coefficient := (-1437403354788828349435215872) }, { argument := 620078807681035515797511864320, coefficient := (-620078807681035515797511864320) }, { argument := 1451523230572608588624166912, coefficient := (-1451523230572608588624166912) }, { argument := 202287139544476670545235017728, coefficient := (-202287139544476670545235017728) }, { argument := 349493229229870503850378526720, coefficient := (-349493229229870503850378526720) }, { argument := 7412963120683522792070578176, coefficient := (-7412963120683522792070578176) }, { argument := 349493229229870503850378526720, coefficient := (-349493229229870503850378526720) }, { argument := 7485782011849372721265770496, coefficient := (-7485782011849372721265770496) }, { argument := 3172453464426152963230549409792, coefficient := (-3172453464426152963230549409792) }, { argument := 126037770249742779238167085056, coefficient := (-126037770249742779238167085056) }, { argument := 5094128736630072785750242361344, coefficient := (-5094128736630072785750242361344) }, { argument := 153835810545961562481360896, coefficient := (-153835810545961562481360896) }] }

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
def constantNumerator : ℤ := 331529395370595449728535966775246848
def positiveArguments : Array ℕ := #[
    41373, 5, 21, 91, 3, 3,
    7, 91, 91, 3, 1123, 45,
    21, 91, 7, 45, 7, 91,
    91, 3, 1, 19, 29, 299,
    9, 29, 9, 9, 771, 9,
    299, 771, 1, 9, 9, 19,
    2325
  ]
def positiveCoefficients : Array ℕ := #[
    3277906767702658439257693857251328, 193428131138340667952988160, 3249592603124123221610201088, 7040783973435600313488769024, 232113757366008801543585792, 3713820117856140824697372672,
    270799383593676935134183424, 7040783973435600313488769024, 7040783973435600313488769024, 3713820117856140824697372672, 86887916507342628044482281472, 6963412720980264046307573760,
    3249592603124123221610201088, 7040783973435600313488769024, 270799383593676935134183424, 6963412720980264046307573760, 270799383593676935134183424, 7040783973435600313488769024,
    7040783973435600313488769024, 232113757366008801543585792, 1237940039285380274899124224, 1470053796651389076442710016, 1121883160602375874127331328, 11567002242072771943588691968,
    1392682544196052809261514752, 1121883160602375874127331328, 1392682544196052809261514752, 1392682544196052809261514752, 59653235643064261996701548544, 1392682544196052809261514752,
    11567002242072771943588691968, 59653235643064261996701548544, 1237940039285380274899124224, 1392682544196052809261514752, 1392682544196052809261514752, 1470053796651389076442710016,
    184205477845664584904989684531200
  ]
def positiveScales : Array ℕ := #[
    15, 2, 4, 6, 1, 1,
    2, 6, 6, 1, 10, 5,
    4, 6, 2, 5, 2, 6,
    6, 1, 0, 4, 4, 8,
    3, 4, 3, 3, 9, 3,
    8, 9, 0, 3, 3, 4,
    11
  ]
def negativeArguments : Array ℕ := #[
    9048975157010165, 257, 739315799, 1285, 279748929, 1000783323,
    69937209, 1051145, 4581, 1051145, 2313, 337,
    994825, 4581, 994825, 2313, 1629, 337,
    2666515, 9671, 2666515, 4883, 5173, 1481,
    14068321, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    5094120143149481828622511636480, 155346967820479848949743616, 6982640298907183128020367966208, 198844118810214206655671828480, 645057112269668015205777408, 2307649229077200250387562496,
    645056897826268158332239872, 19855567666544052872601927680, 173065286864206757791531008, 19855567666544052872601927680, 174765338798039830068461568, 6518528019362080510015700992,
    18791712945283179198860492800, 173065286864206757791531008, 18791712945283179198860492800, 174765338798039830068461568, 126037770249742779238167085056, 6518528019362080510015700992,
    25184522124138304013997178880, 182680025023329355446616064, 25184522124138304013997178880, 184474524286819820627820544, 200120744475727255064161550336, 114586824886353011695350185984,
    66435767560651170022388924416, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    53, 8, 29, 10, 28, 29,
    26, 20, 12, 20, 11, 8,
    19, 12, 19, 11, 10, 8,
    21, 13, 21, 12, 12, 10,
    23, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15336401952259115, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924,
    2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661,
    4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 0, 4247927513443585, 4857980995002857, 8224001674198104,
    3169925001442312, 4857980995002857, 3169925001442312, 3169925001442312, 9590587049914763, 3169925001442312,
    8224001674198104, 9590587049914763, 0, 3169925001442312, 3169925001442312, 4247927513443585,
    11183015000882755
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    53006675832122647, 8005624549193879, 29461615502810259, 10327552644081241, 28059557367050000, 29898482512059889,
    26059556887439009, 20003530264648884, 12161446847518008, 20003530264648884, 11175549550636191, 8396604781181865,
    19924083244126852, 12161446847518008, 19924083244126852, 11175549550636191, 10669770888560475, 8396604781181865,
    21346524012989090, 13239449359519281, 21346524012989090, 12253552062637464, 12336785476203756, 10532355925289620,
    23745946823161392, 0, 0
  ]

abbrev PositiveTerm := Fin 37
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 157486687089 / 250000000000
noncomputable def negativeCeiling : ℝ := 586493449 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5094120143149481828622511636480, coefficient := (-5094120143149481828622511636480) }, { argument := 155346967820479848949743616, coefficient := (-155346967820479848949743616) }, { argument := 6982640298907183128020367966208, coefficient := (-6982640298907183128020367966208) }, { argument := 198844118810214206655671828480, coefficient := (-198844118810214206655671828480) }, { argument := 645057112269668015205777408, coefficient := (-645057112269668015205777408) }, { argument := 2307649229077200250387562496, coefficient := (-2307649229077200250387562496) }, { argument := 645056897826268158332239872, coefficient := (-645056897826268158332239872) }, { argument := 19855567666544052872601927680, coefficient := (-19855567666544052872601927680) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 19855567666544052872601927680, coefficient := (-19855567666544052872601927680) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 6518528019362080510015700992, coefficient := (-6518528019362080510015700992) }, { argument := 18791712945283179198860492800, coefficient := (-18791712945283179198860492800) }, { argument := 173065286864206757791531008, coefficient := (-173065286864206757791531008) }, { argument := 18791712945283179198860492800, coefficient := (-18791712945283179198860492800) }, { argument := 174765338798039830068461568, coefficient := (-174765338798039830068461568) }, { argument := 126037770249742779238167085056, coefficient := (-126037770249742779238167085056) }, { argument := 6518528019362080510015700992, coefficient := (-6518528019362080510015700992) }, { argument := 25184522124138304013997178880, coefficient := (-25184522124138304013997178880) }, { argument := 182680025023329355446616064, coefficient := (-182680025023329355446616064) }, { argument := 25184522124138304013997178880, coefficient := (-25184522124138304013997178880) }, { argument := 184474524286819820627820544, coefficient := (-184474524286819820627820544) }, { argument := 200120744475727255064161550336, coefficient := (-200120744475727255064161550336) }, { argument := 114586824886353011695350185984, coefficient := (-114586824886353011695350185984) }, { argument := 66435767560651170022388924416, coefficient := (-66435767560651170022388924416) }, { argument := 3277906767702658439257693857251328, coefficient := 3277906767702658439257693857251328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 86887916507342628044482281472, coefficient := 86887916507342628044482281472 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 184205477845664584904989684531200, coefficient := 184205477845664584904989684531200 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
