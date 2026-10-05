/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.SignedDyadicLogCanonical
import MatrixMultiplication.RationalDyadicLog

/-!
# Bounded directed term shards, root orientation 4, branch 2

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
Every proof below checks at most 64 signed terms.  The untrusted producer supplies integer
arrays and rational endpoints only; the direction of every logarithm bound is proved by the
committed generic checkers of `SignedDyadicLogCertificate` and `RationalDyadicLog`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (396190434277544630535525612126208)
def positiveArguments : Array ℕ := #[
    375310177, 120967743, 846774201, 846774201, 1310150410433, 2842654329225,
    202175266388285, 25272381951405, 5681494656585, 2614363498927, 8835328693771, 1306619346979,
    631177439319, 2159568505213, 34562849932709, 155396791949, 8835328693771, 323383138987655,
    2886630201, 438023131409979, 1279422177, 412375743, 2844335253, 2886630201,
    1279422177, 12762500559, 1279422177, 323362938162765, 2844335253, 412375743,
    1279422177, 412375743, 2886630201, 2886630201, 8855582212937, 202175266388285,
    7189789435722383, 1797481106909613, 1578432760011, 191500941412649, 323383138987655, 191412619008457,
    846774201, 2886630201, 423387783, 631178041257, 631177439319, 1306619346979,
    191412619008457, 423387783, 518620843922899, 187655391, 60483969, 417184299,
    423387783, 187655391, 1871901297, 187655391, 191400775137269, 417184299,
    60483969, 187655391, 60483969, 423387783
  ]
def positiveCoefficients : Array ℕ := #[
    865406347922204107948949504, 139466312268454381033095168, 976264185879180667231666176, 976264185879180667231666176, 1475098225056340298738696192, 1600272122230104657179443200,
    56907278398113193166593064960, 56908344969556203274701373440, 1599198576143979383630069760, 1471755809947332914890932224, 4973847876620365845393047552, 1471122601042426304602832896,
    1421285240260856125285466112, 77806655322866606787667165184, 77828619038905312574105976832, 1399689868632173785705873408, 4973847876620365845393047552, 182048523030338046883381903360,
    3328058034580485112307122176, 1972680811397639226572704579584, 2950146682668415374279573504, 475436862082926444615303168, 3279295279495056759013244928, 3328058034580485112307122176,
    2950146682668415374279573504, 58856645388112022425709838336, 2950146682668415374279573504, 182037150976907149303275847680, 3279295279495056759013244928, 475436862082926444615303168,
    2950146682668415374279573504, 475436862082926444615303168, 3328058034580485112307122176, 3328058034580485112307122176, 4985249594291483195257913344, 56907278398113193166593064960,
    2023745813974478298820533813248, 2023783810820909947424983744512, 56869033518519385118000283648, 53902723024194076391971487744, 182048523030338046883381903360, 53877862477531104046106017792,
    976264185879180667231666176, 3328058034580485112307122176, 976265759617034455577788416, 1421286595704732375356276736, 1421285240260856125285466112, 1471122601042426304602832896,
    53877862477531104046106017792, 976265759617034455577788416, 583915159859435025337182846976, 865407742957224682233790464, 139466537088147779368255488, 961961499402865452565659648,
    976265759617034455577788416, 865407742957224682233790464, 17265242078501986635639422976, 865407742957224682233790464, 53874528724164297736495038464, 961961499402865452565659648,
    139466537088147779368255488, 865407742957224682233790464, 139466537088147779368255488, 976265759617034455577788416
  ]
def positiveScales : Array ℕ := #[
    28, 26, 29, 29, 40, 41,
    47, 44, 42, 41, 43, 40,
    39, 40, 44, 37, 43, 48,
    31, 48, 30, 28, 31, 31,
    30, 33, 30, 48, 31, 28,
    30, 28, 31, 31, 43, 47,
    52, 50, 40, 47, 48, 47,
    29, 31, 28, 39, 39, 40,
    47, 28, 48, 27, 25, 28,
    28, 27, 30, 27, 47, 28,
    25, 27, 25, 28
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28483508170315956, 26850047151796328, 29657402073959627, 29657402073959627, 40252869586998317, 41370375814578032,
    47522599840789764, 44522626879912973, 42369407654642371, 41249596884846856, 43006420945870350, 40248976045496074,
    39199254682629009, 40973880219720507, 44974287414606756, 37177165764449713, 43006420945870350, 48200237787899344,
    31426739153331853, 48638000387036895, 30252845249686597, 28619384231273654, 31405444374968626, 31426739153331853,
    30252845249686597, 33571191973166868, 30252845249686597, 48200147664028694, 31405444374968626, 28619384231273654,
    30252845249686597, 28619384231273654, 31426739153331853, 31426739153331853, 43009724299166449, 47522599840789764,
    52674870943000724, 50674898030072097, 40521629942938833, 47444344812834512, 48200237787899344, 47443679272044331,
    29657402073959627, 31426739153331853, 28657404399582138, 39199256058490216, 39199254682629009, 40248976045496074,
    47443679272044331, 28657404399582138, 48881673519032755, 27483510495938467, 25850049477418834, 28636109621219580,
    28657404399582138, 27483510495938467, 30801857219377336, 27483510495938467, 47443590000903380, 28636109621219580,
    25850049477418834, 27483510495938467, 25850049477418834, 28657404399582138
  ]
def negativeLogUpperNumerators : Array ℕ := #[]

abbrev PositiveTerm := Fin 64
abbrev NegativeTerm := Fin 0
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 4723184617 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 865406347922204107948949504, coefficient := (865406347922204107948949504) }, { argument := 139466312268454381033095168, coefficient := (139466312268454381033095168) },
    { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) }, { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) },
    { argument := 1475098225056340298738696192, coefficient := (1475098225056340298738696192) }, { argument := 1600272122230104657179443200, coefficient := (1600272122230104657179443200) },
    { argument := 56907278398113193166593064960, coefficient := (56907278398113193166593064960) }, { argument := 56908344969556203274701373440, coefficient := (56908344969556203274701373440) },
    { argument := 1599198576143979383630069760, coefficient := (1599198576143979383630069760) }, { argument := 1471755809947332914890932224, coefficient := (1471755809947332914890932224) },
    { argument := 4973847876620365845393047552, coefficient := (4973847876620365845393047552) }, { argument := 1471122601042426304602832896, coefficient := (1471122601042426304602832896) },
    { argument := 1421285240260856125285466112, coefficient := (1421285240260856125285466112) }, { argument := 77806655322866606787667165184, coefficient := (77806655322866606787667165184) },
    { argument := 77828619038905312574105976832, coefficient := (77828619038905312574105976832) }, { argument := 1399689868632173785705873408, coefficient := (1399689868632173785705873408) },
    { argument := 4973847876620365845393047552, coefficient := (4973847876620365845393047552) }, { argument := 182048523030338046883381903360, coefficient := (182048523030338046883381903360) },
    { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) }, { argument := 1972680811397639226572704579584, coefficient := (1972680811397639226572704579584) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 3279295279495056759013244928, coefficient := (3279295279495056759013244928) }, { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 58856645388112022425709838336, coefficient := (58856645388112022425709838336) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 182037150976907149303275847680, coefficient := (182037150976907149303275847680) },
    { argument := 3279295279495056759013244928, coefficient := (3279295279495056759013244928) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) }, { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) },
    { argument := 4985249594291483195257913344, coefficient := (4985249594291483195257913344) }, { argument := 56907278398113193166593064960, coefficient := (56907278398113193166593064960) },
    { argument := 2023745813974478298820533813248, coefficient := (2023745813974478298820533813248) }, { argument := 2023783810820909947424983744512, coefficient := (2023783810820909947424983744512) },
    { argument := 56869033518519385118000283648, coefficient := (56869033518519385118000283648) }, { argument := 53902723024194076391971487744, coefficient := (53902723024194076391971487744) },
    { argument := 182048523030338046883381903360, coefficient := (182048523030338046883381903360) }, { argument := 53877862477531104046106017792, coefficient := (53877862477531104046106017792) },
    { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) }, { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) },
    { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }, { argument := 1421286595704732375356276736, coefficient := (1421286595704732375356276736) },
    { argument := 1421285240260856125285466112, coefficient := (1421285240260856125285466112) }, { argument := 1471122601042426304602832896, coefficient := (1471122601042426304602832896) },
    { argument := 53877862477531104046106017792, coefficient := (53877862477531104046106017792) }, { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) },
    { argument := 583915159859435025337182846976, coefficient := (583915159859435025337182846976) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 961961499402865452565659648, coefficient := (961961499402865452565659648) },
    { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 17265242078501986635639422976, coefficient := (17265242078501986635639422976) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 53874528724164297736495038464, coefficient := (53874528724164297736495038464) }, { argument := 961961499402865452565659648, coefficient := (961961499402865452565659648) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard10

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (421236490114508650867089611948032)
def positiveArguments : Array ℕ := #[
    423387783, 2619176221493, 25272381951405, 1797481106909613, 224689356947889, 50510794927473,
    518864449859905, 438023131409979, 518620843922899, 375310177, 1279422177, 187655391,
    2159570564739, 2159568505213, 120967743, 412375743, 60483969, 834367253,
    2844335253, 417184299, 846774201, 2886630201, 423387783, 375310177,
    1279422177, 187655391, 3743796559, 12762500559, 1871901297, 375310177,
    1279422177, 187655391, 5681494656585, 1578432760011, 50510794927473, 5677683465843,
    191489097968497, 323362938162765, 191400775137269, 34562882894427, 34562849932709, 834367253,
    2844335253, 417184299, 120967743, 412375743, 60483969, 375310177,
    1279422177, 187655391, 120967743, 412375743, 60483969, 846774201,
    2886630201, 423387783, 846774201, 2886630201, 423387783, 1310150410433,
    8855582212937, 2619176221493, 155396940147, 155396791949
  ]
def positiveCoefficients : Array ℕ := #[
    976265759617034455577788416, 1474465131891692312058658816, 56908344969556203274701373440, 2023783810820909947424983744512, 2023821808449258533658336165888, 56870099303388735582505009152,
    584189435761216390867682590720, 1972680811397639226572704579584, 583915159859435025337182846976, 865406347922204107948949504, 2950146682668415374279573504, 865407742957224682233790464,
    77806729525110816066452324352, 77806655322866606787667165184, 139466312268454381033095168, 475436862082926444615303168, 139466537088147779368255488, 961959948723441756356476928,
    3279295279495056759013244928, 961961499402865452565659648, 976264185879180667231666176, 3328058034580485112307122176, 976265759617034455577788416, 865406347922204107948949504,
    2950146682668415374279573504, 865407742957224682233790464, 17265214246976865426353422336, 58856645388112022425709838336, 17265242078501986635639422976, 865406347922204107948949504,
    2950146682668415374279573504, 865407742957224682233790464, 1599198576143979383630069760, 56869033518519385118000283648, 56870099303388735582505009152, 1598125821318635065870123008,
    53899389391027218236972204032, 182037150976907149303275847680, 53874528724164297736495038464, 77828693262095763719791312896, 77828619038905312574105976832, 961959948723441756356476928,
    3279295279495056759013244928, 961961499402865452565659648, 139466312268454381033095168, 475436862082926444615303168, 139466537088147779368255488, 865406347922204107948949504,
    2950146682668415374279573504, 865407742957224682233790464, 139466312268454381033095168, 475436862082926444615303168, 139466537088147779368255488, 976264185879180667231666176,
    3328058034580485112307122176, 976265759617034455577788416, 976264185879180667231666176, 3328058034580485112307122176, 976265759617034455577788416, 1475098225056340298738696192,
    4985249594291483195257913344, 1474465131891692312058658816, 1399691203481088939811405824, 1399689868632173785705873408
  ]
def positiveScales : Array ℕ := #[
    28, 41, 44, 50, 47, 45,
    48, 48, 48, 28, 30, 27,
    40, 40, 26, 28, 25, 29,
    31, 28, 29, 31, 28, 28,
    30, 27, 31, 33, 30, 28,
    30, 27, 42, 40, 45, 42,
    47, 48, 47, 44, 44, 29,
    31, 28, 26, 28, 25, 28,
    30, 27, 26, 28, 25, 29,
    31, 28, 29, 31, 28, 40,
    43, 41, 37, 37
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28657404399582138, 41252250267951698, 44522626879912973, 50674898030072097, 47674925117192305, 45521656980291898,
    48882351020843259, 48638000387036895, 48881673519032755, 28483508170315956, 30252845249686597, 27483510495938467,
    40973881595581693, 40973880219720507, 26850047151796328, 28619384231273654, 25850049477418834, 29636107295597069,
    31405444374968626, 28636109621219580, 29657402073959627, 31426739153331853, 28657404399582138, 28483508170315956,
    30252845249686597, 27483510495938467, 31801854893754827, 33571191973166868, 30801857219377336, 28483508170315956,
    30252845249686597, 27483510495938467, 42369407654642371, 40521629942938833, 45521656980291898, 42368439558864591,
    47444255586085022, 48200147664028694, 47443590000903380, 44974288790467942, 44974287414606756, 29636107295597069,
    31405444374968626, 28636109621219580, 26850047151796328, 28619384231273654, 25850049477418834, 28483508170315956,
    30252845249686597, 27483510495938467, 26850047151796328, 28619384231273654, 25850049477418834, 29657402073959627,
    31426739153331853, 28657404399582138, 29657402073959627, 31426739153331853, 28657404399582138, 40252869586998317,
    43009724299166449, 41252250267951698, 37177167140310920, 37177165764449713
  ]
def negativeLogUpperNumerators : Array ℕ := #[]

abbrev PositiveTerm := Fin 64
abbrev NegativeTerm := Fin 0
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 949731399 / 200000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }, { argument := 1474465131891692312058658816, coefficient := (1474465131891692312058658816) },
    { argument := 56908344969556203274701373440, coefficient := (56908344969556203274701373440) }, { argument := 2023783810820909947424983744512, coefficient := (2023783810820909947424983744512) },
    { argument := 2023821808449258533658336165888, coefficient := (2023821808449258533658336165888) }, { argument := 56870099303388735582505009152, coefficient := (56870099303388735582505009152) },
    { argument := 584189435761216390867682590720, coefficient := (584189435761216390867682590720) }, { argument := 1972680811397639226572704579584, coefficient := (1972680811397639226572704579584) },
    { argument := 583915159859435025337182846976, coefficient := (583915159859435025337182846976) }, { argument := 865406347922204107948949504, coefficient := (865406347922204107948949504) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 77806729525110816066452324352, coefficient := (77806729525110816066452324352) }, { argument := 77806655322866606787667165184, coefficient := (77806655322866606787667165184) },
    { argument := 139466312268454381033095168, coefficient := (139466312268454381033095168) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 961959948723441756356476928, coefficient := (961959948723441756356476928) },
    { argument := 3279295279495056759013244928, coefficient := (3279295279495056759013244928) }, { argument := 961961499402865452565659648, coefficient := (961961499402865452565659648) },
    { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) }, { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) },
    { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }, { argument := 865406347922204107948949504, coefficient := (865406347922204107948949504) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 17265214246976865426353422336, coefficient := (17265214246976865426353422336) }, { argument := 58856645388112022425709838336, coefficient := (58856645388112022425709838336) },
    { argument := 17265242078501986635639422976, coefficient := (17265242078501986635639422976) }, { argument := 865406347922204107948949504, coefficient := (865406347922204107948949504) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 1599198576143979383630069760, coefficient := (1599198576143979383630069760) }, { argument := 56869033518519385118000283648, coefficient := (56869033518519385118000283648) },
    { argument := 56870099303388735582505009152, coefficient := (56870099303388735582505009152) }, { argument := 1598125821318635065870123008, coefficient := (1598125821318635065870123008) },
    { argument := 53899389391027218236972204032, coefficient := (53899389391027218236972204032) }, { argument := 182037150976907149303275847680, coefficient := (182037150976907149303275847680) },
    { argument := 53874528724164297736495038464, coefficient := (53874528724164297736495038464) }, { argument := 77828693262095763719791312896, coefficient := (77828693262095763719791312896) },
    { argument := 77828619038905312574105976832, coefficient := (77828619038905312574105976832) }, { argument := 961959948723441756356476928, coefficient := (961959948723441756356476928) },
    { argument := 3279295279495056759013244928, coefficient := (3279295279495056759013244928) }, { argument := 961961499402865452565659648, coefficient := (961961499402865452565659648) },
    { argument := 139466312268454381033095168, coefficient := (139466312268454381033095168) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 865406347922204107948949504, coefficient := (865406347922204107948949504) },
    { argument := 2950146682668415374279573504, coefficient := (2950146682668415374279573504) }, { argument := 865407742957224682233790464, coefficient := (865407742957224682233790464) },
    { argument := 139466312268454381033095168, coefficient := (139466312268454381033095168) }, { argument := 475436862082926444615303168, coefficient := (475436862082926444615303168) },
    { argument := 139466537088147779368255488, coefficient := (139466537088147779368255488) }, { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) },
    { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) }, { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) },
    { argument := 976264185879180667231666176, coefficient := (976264185879180667231666176) }, { argument := 3328058034580485112307122176, coefficient := (3328058034580485112307122176) },
    { argument := 976265759617034455577788416, coefficient := (976265759617034455577788416) }, { argument := 1475098225056340298738696192, coefficient := (1475098225056340298738696192) },
    { argument := 4985249594291483195257913344, coefficient := (4985249594291483195257913344) }, { argument := 1474465131891692312058658816, coefficient := (1474465131891692312058658816) },
    { argument := 1399691203481088939811405824, coefficient := (1399691203481088939811405824) }, { argument := 1399689868632173785705873408, coefficient := (1399689868632173785705873408) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard11

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1492550490287298257592609033682944)
def positiveArguments : Array ℕ := #[
    705903828453, 2415244241431, 38654816490383, 173794536263, 453596970055, 3950199765175,
    63725025, 42190088680685, 28244425, 9103575, 62791325, 63725025,
    28244425, 281743975, 28244425, 7899477788815, 62791325, 9103575,
    28244425, 9103575, 63725025, 63725025, 455442258955, 453596970055,
    4025418556563, 4025486696895, 453322435185, 2375683452081, 8128381722587, 130090819992691,
    584896677451, 4025418556563, 561966809192227, 4452730191, 1501385648253641, 1973554407,
    636104313, 4387488723, 4452730191, 1973554407, 19686612969, 1973554407,
    561902449777015, 4387488723, 636104313, 1973554407, 636104313, 4452730191,
    4452730191, 8083049472251, 3950199765175, 561966809192227, 35123588605521, 15790121689329,
    63725025, 4452730191, 556591581, 127447047, 705903828453, 2375683452081,
    352739580597, 352739580597, 1206895622919
  ]
def positiveCoefficients : Array ℕ := #[
    794777054695084332964380672, 43509172262869551506840879104, 43521454285540945694390484992, 782701008753074954408296448, 127676196582255252031406080, 4447529547620287700480819200,
    146939903408217877433548800, 47501816915265286800083517440, 130254419871020975600435200, 20991414772602553919078400, 144786937790515051390566400, 146939903408217877433548800,
    130254419871020975600435200, 2598629500567311033879756800, 130254419871020975600435200, 4447010653266092961856225280, 144786937790515051390566400, 20991414772602553919078400,
    130254419871020975600435200, 20991414772602553919078400, 146939903408217877433548800, 146939903408217877433548800, 128195599232407184059924480, 127676196582255252031406080,
    4532218377836851668883341312, 4532295097030302694354452480, 127598921886115739058831360, 2674781777385561297512300544, 146427907587871854358962372608, 146469242110851364692567261184,
    2634140458618564790185885696, 4532218377836851668883341312, 158179594529543758964863270912, 5133648391416053115352252416, 1690409961503627046531821993984, 4550706632683827303718846464,
    733378341630864730764607488, 5058430099966733655786651648, 5133648391416053115352252416, 4550706632683827303718846464, 90788477779328587695680126976, 4550706632683827303718846464,
    158161478964645849825374371840, 5058430099966733655786651648, 733378341630864730764607488, 4550706632683827303718846464, 733378341630864730764607488, 5133648391416053115352252416,
    5133648391416053115352252416, 4550352323905860993456013312, 4447529547620287700480819200, 158179594529543758964863270912, 158182580555738974824658108416, 4444524134762304450355789824,
    146939903408217877433548800, 5133648391416053115352252416, 5133651224144189934375272448, 146936441184939543072079872, 794777054695084332964380672, 2674781777385561297512300544,
    794298921867737120485933056, 794298921867737120485933056, 43482997421224728415375982592
  ]
def positiveScales : Array ℕ := #[
    39, 41, 45, 37, 38, 41,
    25, 45, 24, 23, 25, 25,
    24, 28, 24, 42, 25, 23,
    24, 23, 25, 25, 38, 38,
    41, 41, 38, 41, 42, 46,
    39, 41, 48, 32, 50, 30,
    29, 32, 32, 30, 34, 30,
    48, 32, 29, 30, 29, 32,
    32, 42, 41, 48, 44, 43,
    25, 32, 29, 26, 39, 41,
    38, 38, 40
  ]
def negativeArguments : Array ℕ := #[
    107
  ]
def negativeCoefficients : Array ℕ := #[
    16954826778052568245018405371904
  ]
def negativeScales : Array ℕ := #[
    6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    39360680689488578, 41135306227537219, 45135713422429878, 37338591771309282, 38722620047126083, 41845062752078506,
    25925356698021485, 45261969353542607, 24751462794783959, 23118001776386014, 25904061919790111, 25925356698021485,
    24751462794783959, 28069809518278787, 24751462794783959, 42844894422677753, 25904061919790111, 23118001776386014,
    24751462794783959, 23118001776386014, 25925356698021485, 25925356698021485, 38728477204256890, 38722620047126083,
    41872275938627708, 41872300359662529, 38721746606541965, 41111479755705841, 42886105293544419, 46886512488435516,
    39089390837526544, 41872275938627708, 48997478251723751, 32052043049665745, 50415216020763067, 30878149145838892,
    29244688127608141, 32030748271302517, 32052043049665745, 30878149145838892, 34196495869500914, 30878149145838892,
    48997313017188780, 32030748271302517, 29244688127608141, 30878149145838892, 29244688127608141, 32052043049665745,
    32052043049665745, 42878036816159916, 41845062752078506, 48997478251723751, 44997505485858719, 43844087523062134,
    25925356698021485, 32052043049665745, 29052043845739297, 26925322704592550, 39360680689488578, 41111479755705841,
    38359812512145405, 38359812512145405, 40134438050194045
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6741466986587556
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 69116433 / 40000000000
noncomputable def negativeCeiling : ℝ := 1375841079 / 1000000000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 16954826778052568245018405371904, coefficient := (-16954826778052568245018405371904) }, { argument := 794777054695084332964380672, coefficient := (794777054695084332964380672) },
    { argument := 43509172262869551506840879104, coefficient := (43509172262869551506840879104) }, { argument := 43521454285540945694390484992, coefficient := (43521454285540945694390484992) },
    { argument := 782701008753074954408296448, coefficient := (782701008753074954408296448) }, { argument := 127676196582255252031406080, coefficient := (127676196582255252031406080) },
    { argument := 4447529547620287700480819200, coefficient := (4447529547620287700480819200) }, { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) },
    { argument := 47501816915265286800083517440, coefficient := (47501816915265286800083517440) }, { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 144786937790515051390566400, coefficient := (144786937790515051390566400) },
    { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) }, { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) },
    { argument := 2598629500567311033879756800, coefficient := (2598629500567311033879756800) }, { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) },
    { argument := 4447010653266092961856225280, coefficient := (4447010653266092961856225280) }, { argument := 144786937790515051390566400, coefficient := (144786937790515051390566400) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) },
    { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) }, { argument := 128195599232407184059924480, coefficient := (128195599232407184059924480) },
    { argument := 127676196582255252031406080, coefficient := (127676196582255252031406080) }, { argument := 4532218377836851668883341312, coefficient := (4532218377836851668883341312) },
    { argument := 4532295097030302694354452480, coefficient := (4532295097030302694354452480) }, { argument := 127598921886115739058831360, coefficient := (127598921886115739058831360) },
    { argument := 2674781777385561297512300544, coefficient := (2674781777385561297512300544) }, { argument := 146427907587871854358962372608, coefficient := (146427907587871854358962372608) },
    { argument := 146469242110851364692567261184, coefficient := (146469242110851364692567261184) }, { argument := 2634140458618564790185885696, coefficient := (2634140458618564790185885696) },
    { argument := 4532218377836851668883341312, coefficient := (4532218377836851668883341312) }, { argument := 158179594529543758964863270912, coefficient := (158179594529543758964863270912) },
    { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) }, { argument := 1690409961503627046531821993984, coefficient := (1690409961503627046531821993984) },
    { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 5058430099966733655786651648, coefficient := (5058430099966733655786651648) }, { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) },
    { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) }, { argument := 90788477779328587695680126976, coefficient := (90788477779328587695680126976) },
    { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) }, { argument := 158161478964645849825374371840, coefficient := (158161478964645849825374371840) },
    { argument := 5058430099966733655786651648, coefficient := (5058430099966733655786651648) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) }, { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) },
    { argument := 4550352323905860993456013312, coefficient := (4550352323905860993456013312) }, { argument := 4447529547620287700480819200, coefficient := (4447529547620287700480819200) },
    { argument := 158179594529543758964863270912, coefficient := (158179594529543758964863270912) }, { argument := 158182580555738974824658108416, coefficient := (158182580555738974824658108416) },
    { argument := 4444524134762304450355789824, coefficient := (4444524134762304450355789824) }, { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) },
    { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) }, { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) },
    { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) }, { argument := 794777054695084332964380672, coefficient := (794777054695084332964380672) },
    { argument := 2674781777385561297512300544, coefficient := (2674781777385561297512300544) }, { argument := 794298921867737120485933056, coefficient := (794298921867737120485933056) },
    { argument := 794298921867737120485933056, coefficient := (794298921867737120485933056) }, { argument := 43482997421224728415375982592, coefficient := (43482997421224728415375982592) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard12

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (323579444086816428860588899172352)
def positiveArguments : Array ℕ := #[
    19315780999167, 86844991287, 4025486696895, 35123588605521, 556591581, 375353717809869,
    246694437, 79513083, 548436393, 556591581, 246694437, 2460827979,
    246694437, 70239132285723, 548436393, 79513083, 246694437, 79513083,
    556591581, 556591581, 4041592873875, 42190088680685, 1501385648253641, 375353717809869,
    21080340843147, 28244425, 1973554407, 246694437, 56487519, 2415244241431,
    8128381722587, 1206895622919, 9103575, 636104313, 79513083, 18206721,
    62791325, 4387488723, 548436393, 125579691, 63725025, 4452730191,
    556591581, 127447047, 28244425, 1973554407, 246694437, 56487519,
    281743975, 19686612969, 2460827979, 563474673, 28244425, 1973554407,
    246694437, 56487519, 453322435185, 15790121689329, 127447047, 21080340843147,
    56487519, 18206721, 125579691, 127447047
  ]
def positiveCoefficients : Array ℕ := #[
    43495272055109304053888188416, 782230140798254343681736704, 4532295097030302694354452480, 158182580555738974824658108416, 5133651224144189934375272448, 1690442863660656336352548225024,
    4550709143746864337431560192, 733378746306312847767896064, 5058432891189696308963180544, 5133651224144189934375272448, 4550709143746864337431560192, 90788527876073805872394928128,
    4550709143746864337431560192, 158164464994404538890326114304, 5058432891189696308963180544, 733378746306312847767896064, 4550709143746864337431560192, 733378746306312847767896064,
    5133651224144189934375272448, 5133651224144189934375272448, 4550429040191675509506048000, 47501816915265286800083517440, 1690409961503627046531821993984, 1690442863660656336352548225024,
    47468707583019938333595795456, 130254419871020975600435200, 4550706632683827303718846464, 4550709143746864337431560192, 130251350793975712173785088, 43509172262869551506840879104,
    146427907587871854358962372608, 43482997421224728415375982592, 20991414772602553919078400, 733378341630864730764607488, 733378746306312847767896064, 20990920169277077581725696,
    144786937790515051390566400, 5058430099966733655786651648, 5058432891189696308963180544, 144783526295782919730364416, 146939903408217877433548800, 5133648391416053115352252416,
    5133651224144189934375272448, 146936441184939543072079872, 130254419871020975600435200, 4550706632683827303718846464, 4550709143746864337431560192, 130251350793975712173785088,
    2598629500567311033879756800, 90788477779328587695680126976, 90788527876073805872394928128, 2598568271212044373450555392, 130254419871020975600435200, 4550706632683827303718846464,
    4550709143746864337431560192, 130251350793975712173785088, 127598921886115739058831360, 4444524134762304450355789824, 146936441184939543072079872, 47468707583019938333595795456,
    130251350793975712173785088, 20990920169277077581725696, 144783526295782919730364416, 146936441184939543072079872
  ]
def positiveScales : Array ℕ := #[
    44, 36, 41, 44, 29, 48,
    27, 26, 29, 29, 27, 31,
    27, 45, 29, 26, 27, 26,
    29, 29, 41, 45, 50, 48,
    44, 24, 30, 27, 25, 41,
    42, 40, 23, 29, 26, 24,
    25, 32, 29, 26, 25, 32,
    29, 26, 24, 30, 27, 25,
    28, 34, 31, 29, 24, 30,
    27, 25, 38, 43, 26, 44,
    25, 24, 26, 26
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    44134845245086705, 36337723593966108, 41872300359662529, 44997505485858719, 29052043845739297, 48415244101121034,
    27878149941912441, 26244688923681692, 29030749067376068, 29052043845739297, 27878149941912441, 31196496665574465,
    27878149941912441, 45997340254475579, 29030749067376068, 26244688923681692, 27878149941912441, 26244688923681692,
    29052043845739297, 29052043845739297, 41878061138951621, 45261969353542607, 50415216020763067, 48415244101121034,
    44260963427301279, 24751462794783959, 30878149145838892, 27878149941912441, 25751428801354786, 41135306227537219,
    42886105293544419, 40134438050194045, 23118001776386014, 29244688127608141, 26244688923681692, 24117967782956830,
    25904061919790111, 32030748271302517, 29030749067376068, 26904027926361103, 25925356698021485, 32052043049665745,
    29052043845739297, 26925322704592550, 24751462794783959, 30878149145838892, 27878149941912441, 25751428801354786,
    28069809518278787, 34196495869500914, 31196496665574465, 29069775524849603, 24751462794783959, 30878149145838892,
    27878149941912441, 25751428801354786, 38721746606541965, 43844087523062134, 26925322704592550, 44260963427301279,
    25751428801354786, 24117967782956830, 26904027926361103, 26925322704592550
  ]
def negativeLogUpperNumerators : Array ℕ := #[]

abbrev PositiveTerm := Fin 64
abbrev NegativeTerm := Fin 0
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 3537536939 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 43495272055109304053888188416, coefficient := (43495272055109304053888188416) }, { argument := 782230140798254343681736704, coefficient := (782230140798254343681736704) },
    { argument := 4532295097030302694354452480, coefficient := (4532295097030302694354452480) }, { argument := 158182580555738974824658108416, coefficient := (158182580555738974824658108416) },
    { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) }, { argument := 1690442863660656336352548225024, coefficient := (1690442863660656336352548225024) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) },
    { argument := 5058432891189696308963180544, coefficient := (5058432891189696308963180544) }, { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 90788527876073805872394928128, coefficient := (90788527876073805872394928128) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 158164464994404538890326114304, coefficient := (158164464994404538890326114304) },
    { argument := 5058432891189696308963180544, coefficient := (5058432891189696308963180544) }, { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) },
    { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) }, { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) },
    { argument := 4550429040191675509506048000, coefficient := (4550429040191675509506048000) }, { argument := 47501816915265286800083517440, coefficient := (47501816915265286800083517440) },
    { argument := 1690409961503627046531821993984, coefficient := (1690409961503627046531821993984) }, { argument := 1690442863660656336352548225024, coefficient := (1690442863660656336352548225024) },
    { argument := 47468707583019938333595795456, coefficient := (47468707583019938333595795456) }, { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) },
    { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) }, { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) },
    { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) }, { argument := 43509172262869551506840879104, coefficient := (43509172262869551506840879104) },
    { argument := 146427907587871854358962372608, coefficient := (146427907587871854358962372608) }, { argument := 43482997421224728415375982592, coefficient := (43482997421224728415375982592) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 144786937790515051390566400, coefficient := (144786937790515051390566400) }, { argument := 5058430099966733655786651648, coefficient := (5058430099966733655786651648) },
    { argument := 5058432891189696308963180544, coefficient := (5058432891189696308963180544) }, { argument := 144783526295782919730364416, coefficient := (144783526295782919730364416) },
    { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) }, { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) },
    { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) }, { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) },
    { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) }, { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) },
    { argument := 2598629500567311033879756800, coefficient := (2598629500567311033879756800) }, { argument := 90788477779328587695680126976, coefficient := (90788477779328587695680126976) },
    { argument := 90788527876073805872394928128, coefficient := (90788527876073805872394928128) }, { argument := 2598568271212044373450555392, coefficient := (2598568271212044373450555392) },
    { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) }, { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) },
    { argument := 127598921886115739058831360, coefficient := (127598921886115739058831360) }, { argument := 4444524134762304450355789824, coefficient := (4444524134762304450355789824) },
    { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) }, { argument := 47468707583019938333595795456, coefficient := (47468707583019938333595795456) },
    { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 144783526295782919730364416, coefficient := (144783526295782919730364416) }, { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard13

namespace TermShard14

/-! Directed signed-log shard 14.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-915087687012300920948228232314880)
def positiveArguments : Array ℕ := #[
    56487519, 563474673, 56487519, 15788278201491, 125579691, 18206721,
    56487519, 18206721, 127447047, 127447047, 455167726515, 7899477788815,
    561902449777015, 70239132285723, 15788278201491, 38654816490383, 130090819992691, 19315780999167,
    62791325, 4387488723, 548436393, 125579691, 9103575, 636104313,
    79513083, 18206721, 28244425, 1973554407, 246694437, 56487519,
    9103575, 636104313, 79513083, 18206721, 63725025, 4452730191,
    556591581, 127447047, 63725025, 4452730191, 556591581, 127447047,
    455442258955, 8083049472251, 4041592873875, 455167726515, 173794536263, 584896677451,
    86844991287, 271749424635, 929788459145, 14880814803985, 66905098585, 26758670705,
    1048481315287, 90355976505, 1048486168785, 26754021223, 9827095021911, 33623326159997,
    538125080774821, 2419444906381, 1048481315287
  ]
def positiveCoefficients : Array ℕ := #[
    130251350793975712173785088, 2598568271212044373450555392, 130251350793975712173785088, 4444005239066037022774788096, 144783526295782919730364416, 20990920169277077581725696,
    130251350793975712173785088, 20990920169277077581725696, 146936441184939543072079872, 146936441184939543072079872, 128118325220251864494243840, 4447010653266092961856225280,
    158161478964645849825374371840, 158164464994404538890326114304, 4444005239066037022774788096, 43521454285540945694390484992, 146469242110851364692567261184, 43495272055109304053888188416,
    144786937790515051390566400, 5058430099966733655786651648, 5058432891189696308963180544, 144783526295782919730364416, 20991414772602553919078400, 733378341630864730764607488,
    733378746306312847767896064, 20990920169277077581725696, 130254419871020975600435200, 4550706632683827303718846464, 4550709143746864337431560192, 130251350793975712173785088,
    20991414772602553919078400, 733378341630864730764607488, 733378746306312847767896064, 20990920169277077581725696, 146939903408217877433548800, 5133648391416053115352252416,
    5133651224144189934375272448, 146936441184939543072079872, 146939903408217877433548800, 5133648391416053115352252416, 5133651224144189934375272448, 146936441184939543072079872,
    128195599232407184059924480, 4550352323905860993456013312, 4550429040191675509506048000, 128118325220251864494243840, 782701008753074954408296448, 2634140458618564790185885696,
    782230140798254343681736704, 76490662970270792873410560, 4187394958138809643874385920, 4188577000387262904700764160, 75328444264148074800087040, 7531896213497987968532480,
    295121253801966295708598272, 3255417136948922332049571840, 295122619940202810924072960, 7530587500660321354252288, 2766081342425802239027183616, 151425999165119139370093248512,
    151468744578512619782407192576, 2724052794705229044980383744, 295121253801966295708598272
  ]
def positiveScales : Array ℕ := #[
    25, 29, 25, 43, 26, 24,
    25, 24, 26, 26, 38, 42,
    48, 45, 43, 45, 46, 44,
    25, 32, 29, 26, 23, 29,
    26, 24, 24, 30, 27, 25,
    23, 29, 26, 24, 25, 32,
    29, 26, 25, 32, 29, 26,
    38, 42, 41, 38, 37, 39,
    36, 37, 39, 43, 35, 34,
    39, 36, 39, 34, 43, 44,
    48, 41, 39
  ]
def negativeArguments : Array ℕ := #[
    31
  ]
def negativeCoefficients : Array ℕ := #[
    9824292151768777861599449841664
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    25751428801354786, 29069775524849603, 25751428801354786, 43843919079393730, 26904027926361103, 24117967782956830,
    25751428801354786, 24117967782956830, 26925322704592550, 26925322704592550, 38727607311310416, 42844894422677753,
    48997313017188780, 45997340254475579, 43843919079393730, 45135713422429878, 46886512488435516, 44134845245086705,
    25904061919790111, 32030748271302517, 29030749067376068, 26904027926361103, 23118001776386014, 29244688127608141,
    26244688923681692, 24117967782956830, 24751462794783959, 30878149145838892, 27878149941912441, 25751428801354786,
    23118001776386014, 29244688127608141, 26244688923681692, 24117967782956830, 25925356698021485, 32052043049665745,
    29052043845739297, 26925322704592550, 25925356698021485, 32052043049665745, 29052043845739297, 26925322704592550,
    38728477204256890, 42878036816159916, 41878061138951621, 38727607311310416, 37338591771309282, 39089390837526544,
    36337723593966108, 37983486023332533, 39758111562483990, 43758518757376503, 35961397105493867, 34639287397627094,
    39931438289949636, 36394900978729001, 39931444968276785, 34639036698796625, 43159902144545818, 44934527682099903,
    48934934876989094, 41137813226366522, 39931438289949636
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4954196321574415
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 260543561 / 500000000000
noncomputable def negativeCeiling : ℝ := 292930767 / 500000000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) }, { argument := 2598568271212044373450555392, coefficient := (2598568271212044373450555392) },
    { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) }, { argument := 4444005239066037022774788096, coefficient := (4444005239066037022774788096) },
    { argument := 144783526295782919730364416, coefficient := (144783526295782919730364416) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) }, { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) },
    { argument := 128118325220251864494243840, coefficient := (128118325220251864494243840) }, { argument := 4447010653266092961856225280, coefficient := (4447010653266092961856225280) },
    { argument := 158161478964645849825374371840, coefficient := (158161478964645849825374371840) }, { argument := 158164464994404538890326114304, coefficient := (158164464994404538890326114304) },
    { argument := 4444005239066037022774788096, coefficient := (4444005239066037022774788096) }, { argument := 43521454285540945694390484992, coefficient := (43521454285540945694390484992) },
    { argument := 146469242110851364692567261184, coefficient := (146469242110851364692567261184) }, { argument := 43495272055109304053888188416, coefficient := (43495272055109304053888188416) },
    { argument := 144786937790515051390566400, coefficient := (144786937790515051390566400) }, { argument := 5058430099966733655786651648, coefficient := (5058430099966733655786651648) },
    { argument := 5058432891189696308963180544, coefficient := (5058432891189696308963180544) }, { argument := 144783526295782919730364416, coefficient := (144783526295782919730364416) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 130254419871020975600435200, coefficient := (130254419871020975600435200) }, { argument := 4550706632683827303718846464, coefficient := (4550706632683827303718846464) },
    { argument := 4550709143746864337431560192, coefficient := (4550709143746864337431560192) }, { argument := 130251350793975712173785088, coefficient := (130251350793975712173785088) },
    { argument := 20991414772602553919078400, coefficient := (20991414772602553919078400) }, { argument := 733378341630864730764607488, coefficient := (733378341630864730764607488) },
    { argument := 733378746306312847767896064, coefficient := (733378746306312847767896064) }, { argument := 20990920169277077581725696, coefficient := (20990920169277077581725696) },
    { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) }, { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) },
    { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) }, { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) },
    { argument := 146939903408217877433548800, coefficient := (146939903408217877433548800) }, { argument := 5133648391416053115352252416, coefficient := (5133648391416053115352252416) },
    { argument := 5133651224144189934375272448, coefficient := (5133651224144189934375272448) }, { argument := 146936441184939543072079872, coefficient := (146936441184939543072079872) },
    { argument := 128195599232407184059924480, coefficient := (128195599232407184059924480) }, { argument := 4550352323905860993456013312, coefficient := (4550352323905860993456013312) },
    { argument := 4550429040191675509506048000, coefficient := (4550429040191675509506048000) }, { argument := 128118325220251864494243840, coefficient := (128118325220251864494243840) },
    { argument := 782701008753074954408296448, coefficient := (782701008753074954408296448) }, { argument := 2634140458618564790185885696, coefficient := (2634140458618564790185885696) },
    { argument := 782230140798254343681736704, coefficient := (782230140798254343681736704) }, { argument := 9824292151768777861599449841664, coefficient := (-9824292151768777861599449841664) },
    { argument := 76490662970270792873410560, coefficient := (76490662970270792873410560) }, { argument := 4187394958138809643874385920, coefficient := (4187394958138809643874385920) },
    { argument := 4188577000387262904700764160, coefficient := (4188577000387262904700764160) }, { argument := 75328444264148074800087040, coefficient := (75328444264148074800087040) },
    { argument := 7531896213497987968532480, coefficient := (7531896213497987968532480) }, { argument := 295121253801966295708598272, coefficient := (295121253801966295708598272) },
    { argument := 3255417136948922332049571840, coefficient := (3255417136948922332049571840) }, { argument := 295122619940202810924072960, coefficient := (295122619940202810924072960) },
    { argument := 7530587500660321354252288, coefficient := (7530587500660321354252288) }, { argument := 2766081342425802239027183616, coefficient := (2766081342425802239027183616) },
    { argument := 151425999165119139370093248512, coefficient := (151425999165119139370093248512) }, { argument := 151468744578512619782407192576, coefficient := (151468744578512619782407192576) },
    { argument := 2724052794705229044980383744, coefficient := (2724052794705229044980383744) }, { argument := 295121253801966295708598272, coefficient := (295121253801966295708598272) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard14

namespace TermShard15

/-! Directed signed-log shard 15.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-126943995900740068393809187176448)
def positiveArguments : Array ℕ := #[
    20557992355649, 113390703875239, 10279043633663, 1048299199759, 271749424635, 9827095021911,
    2456861412699, 135698795937, 2456861412699, 8406131458473, 134536070243889, 604882807929,
    90355976505, 113390703875239, 312712616900945, 113391227293795, 1445444519753, 929788459145,
    33623326159997, 8406131458473, 464292333099, 135698795937, 464292333099, 7430774339907,
    33409238427, 1048486168785, 10279043633663, 113391227293795, 20558182179445, 1048304052413,
    14880814803985, 538125080774821, 134536070243889, 7430774339907, 26754021223, 1048299199759,
    1445444519753, 1048304052413, 26749372549, 66905098585, 2419444906381, 604882807929,
    33409238427, 3837655719, 13130508013, 210147433109, 944836349, 1159908341697,
    3968617012619, 63515796751267, 285571099387, 3837655719, 1159908341697, 3191761497519,
    1159914361077, 15347914155, 3191761497519, 10920586156613, 174778702132909, 785816264149,
    13130508013, 3968617012619, 10920586156613
  ]
def positiveCoefficients : Array ℕ := #[
    11573120839048292709840191488, 127666582929951154289703387136, 11573174269572438998449651712, 295069992837963846887931904, 76490662970270792873410560, 2766081342425802239027183616,
    2766180035683041697308082176, 76391630852062272074809344, 2766180035683041697308082176, 151431402016025627481637650432, 151474148954567343827620724736, 2724149988391863703289462784,
    3255417136948922332049571840, 127666582929951154289703387136, 1408332424949148571658847518720, 127667172246854594390476718080, 3254851700272168172460703744, 4187394958138809643874385920,
    151425999165119139370093248512, 151431402016025627481637650432, 4181973556671269212633694208, 76391630852062272074809344, 4181973556671269212633694208, 4183154068534926073065897984,
    75230916865284627964624896, 295122619940202810924072960, 11573174269572438998449651712, 127667172246854594390476718080, 11573227700345409166471331840, 295071358738635481759612928,
    4188577000387262904700764160, 151468744578512619782407192576, 151474148954567343827620724736, 4183154068534926073065897984, 7530587500660321354252288, 295069992837963846887931904,
    3254851700272168172460703744, 295071358738635481759612928, 7529279015254435922182144, 75328444264148074800087040, 2724052794705229044980383744, 2724149988391863703289462784,
    75230916865284627964624896, 8641632433032326453133312, 473076407956256894782275584, 473209950721279316860076032, 8510329258564999821918208, 326485173465658696749023232,
    17873062099207139421820289024, 17878107411321638850660401152, 321524474196769019671871488, 8641632433032326453133312, 326485173465658696749023232, 3593603972720516173299449856,
    326486867770504009337536512, 8640107558671545123471360, 3593603972720516173299449856, 196727790982358815488125960192, 196783324449516971712594313216, 3539001834403111655025147904,
    473076407956256894782275584, 17873062099207139421820289024, 196727790982358815488125960192
  ]
def positiveScales : Array ℕ := #[
    44, 46, 43, 39, 37, 43,
    41, 36, 41, 42, 46, 39,
    36, 46, 48, 46, 40, 39,
    44, 42, 38, 36, 38, 42,
    34, 39, 43, 46, 44, 39,
    43, 48, 46, 42, 34, 39,
    40, 39, 34, 35, 41, 39,
    34, 31, 33, 37, 29, 40,
    41, 45, 38, 31, 40, 41,
    40, 33, 41, 43, 47, 39,
    33, 41, 43
  ]
def negativeArguments : Array ℕ := #[
    41
  ]
def negativeCoefficients : Array ℕ := #[
    3248354663084837841335301963776
  ]
def negativeScales : Array ℕ := #[
    5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    44224764614800326, 46688295696893509, 43224771275386987, 39931187679868352, 37983486023332533, 43159902144545818,
    41159953618712736, 36981616962374827, 41159953618712736, 42934579156266383, 46934986351155571, 39137864700533439,
    36394900978729001, 46688295696893509, 48151830756746525, 46688302356448360, 40394650373811773, 39758111562483990,
    44934527682099903, 42934579156266383, 38756242501493485, 36981616962374827, 38756242501493485, 42756649696386003,
    34959528044526573, 39931444968276785, 43224771275386987, 46688302356448360, 44224777935973915, 39931194358194160,
    43758518757376503, 48934934876989094, 46934986351155571, 42756649696386003, 34639036698796625, 39931187679868352,
    40394650373811773, 39931194358194160, 34638785999972854, 35961397105493867, 41137813226366522, 39137864700533439,
    34959528044526573, 31837578145224033, 33612203683356612, 37612610878249266, 29815489227074474, 40077147943825510,
    41851773481763273, 45852180676655071, 38055059025646213, 31837578145224033, 40077147943825510, 41537489989706644,
    40077155430716353, 33837323549485241, 41537489989706644, 43312115527755341, 47312522722648001, 39515401071527376,
    33612203683356612, 41851773481763273, 43312115527755341
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5357552004618085
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 2004028187 / 1000000000000
noncomputable def negativeCeiling : ℝ := 167587 / 800000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 11573120839048292709840191488, coefficient := (11573120839048292709840191488) }, { argument := 127666582929951154289703387136, coefficient := (127666582929951154289703387136) },
    { argument := 11573174269572438998449651712, coefficient := (11573174269572438998449651712) }, { argument := 295069992837963846887931904, coefficient := (295069992837963846887931904) },
    { argument := 76490662970270792873410560, coefficient := (76490662970270792873410560) }, { argument := 2766081342425802239027183616, coefficient := (2766081342425802239027183616) },
    { argument := 2766180035683041697308082176, coefficient := (2766180035683041697308082176) }, { argument := 76391630852062272074809344, coefficient := (76391630852062272074809344) },
    { argument := 2766180035683041697308082176, coefficient := (2766180035683041697308082176) }, { argument := 151431402016025627481637650432, coefficient := (151431402016025627481637650432) },
    { argument := 151474148954567343827620724736, coefficient := (151474148954567343827620724736) }, { argument := 2724149988391863703289462784, coefficient := (2724149988391863703289462784) },
    { argument := 3255417136948922332049571840, coefficient := (3255417136948922332049571840) }, { argument := 127666582929951154289703387136, coefficient := (127666582929951154289703387136) },
    { argument := 1408332424949148571658847518720, coefficient := (1408332424949148571658847518720) }, { argument := 127667172246854594390476718080, coefficient := (127667172246854594390476718080) },
    { argument := 3254851700272168172460703744, coefficient := (3254851700272168172460703744) }, { argument := 4187394958138809643874385920, coefficient := (4187394958138809643874385920) },
    { argument := 151425999165119139370093248512, coefficient := (151425999165119139370093248512) }, { argument := 151431402016025627481637650432, coefficient := (151431402016025627481637650432) },
    { argument := 4181973556671269212633694208, coefficient := (4181973556671269212633694208) }, { argument := 76391630852062272074809344, coefficient := (76391630852062272074809344) },
    { argument := 4181973556671269212633694208, coefficient := (4181973556671269212633694208) }, { argument := 4183154068534926073065897984, coefficient := (4183154068534926073065897984) },
    { argument := 75230916865284627964624896, coefficient := (75230916865284627964624896) }, { argument := 295122619940202810924072960, coefficient := (295122619940202810924072960) },
    { argument := 11573174269572438998449651712, coefficient := (11573174269572438998449651712) }, { argument := 127667172246854594390476718080, coefficient := (127667172246854594390476718080) },
    { argument := 11573227700345409166471331840, coefficient := (11573227700345409166471331840) }, { argument := 295071358738635481759612928, coefficient := (295071358738635481759612928) },
    { argument := 4188577000387262904700764160, coefficient := (4188577000387262904700764160) }, { argument := 151468744578512619782407192576, coefficient := (151468744578512619782407192576) },
    { argument := 151474148954567343827620724736, coefficient := (151474148954567343827620724736) }, { argument := 4183154068534926073065897984, coefficient := (4183154068534926073065897984) },
    { argument := 7530587500660321354252288, coefficient := (7530587500660321354252288) }, { argument := 295069992837963846887931904, coefficient := (295069992837963846887931904) },
    { argument := 3254851700272168172460703744, coefficient := (3254851700272168172460703744) }, { argument := 295071358738635481759612928, coefficient := (295071358738635481759612928) },
    { argument := 7529279015254435922182144, coefficient := (7529279015254435922182144) }, { argument := 75328444264148074800087040, coefficient := (75328444264148074800087040) },
    { argument := 2724052794705229044980383744, coefficient := (2724052794705229044980383744) }, { argument := 2724149988391863703289462784, coefficient := (2724149988391863703289462784) },
    { argument := 75230916865284627964624896, coefficient := (75230916865284627964624896) }, { argument := 3248354663084837841335301963776, coefficient := (-3248354663084837841335301963776) },
    { argument := 8641632433032326453133312, coefficient := (8641632433032326453133312) }, { argument := 473076407956256894782275584, coefficient := (473076407956256894782275584) },
    { argument := 473209950721279316860076032, coefficient := (473209950721279316860076032) }, { argument := 8510329258564999821918208, coefficient := (8510329258564999821918208) },
    { argument := 326485173465658696749023232, coefficient := (326485173465658696749023232) }, { argument := 17873062099207139421820289024, coefficient := (17873062099207139421820289024) },
    { argument := 17878107411321638850660401152, coefficient := (17878107411321638850660401152) }, { argument := 321524474196769019671871488, coefficient := (321524474196769019671871488) },
    { argument := 8641632433032326453133312, coefficient := (8641632433032326453133312) }, { argument := 326485173465658696749023232, coefficient := (326485173465658696749023232) },
    { argument := 3593603972720516173299449856, coefficient := (3593603972720516173299449856) }, { argument := 326486867770504009337536512, coefficient := (326486867770504009337536512) },
    { argument := 8640107558671545123471360, coefficient := (8640107558671545123471360) }, { argument := 3593603972720516173299449856, coefficient := (3593603972720516173299449856) },
    { argument := 196727790982358815488125960192, coefficient := (196727790982358815488125960192) }, { argument := 196783324449516971712594313216, coefficient := (196783324449516971712594313216) },
    { argument := 3539001834403111655025147904, coefficient := (3539001834403111655025147904) }, { argument := 473076407956256894782275584, coefficient := (473076407956256894782275584) },
    { argument := 17873062099207139421820289024, coefficient := (17873062099207139421820289024) }, { argument := 196727790982358815488125960192, coefficient := (196727790982358815488125960192) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard15

namespace TermShard16

/-! Directed signed-log shard 16.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-78529580449340972720063797788672)
def positiveArguments : Array ℕ := #[
    3968637607879, 52512764185, 1159914361077, 3968637607879, 63516126368447, 285572581367,
    210147433109, 63515796751267, 174778702132909, 63516126368447, 840441404705, 15347914155,
    52512764185, 840441404705, 3778678505, 944836349, 285571099387, 785816264149,
    285572581367, 3778678505
  ]
def positiveCoefficients : Array ℕ := #[
    17873154852012401020301737984, 472992930431521456148971520, 326486867770504009337536512, 17873154852012401020301737984, 17878200190309702782767071232, 321526142757912962303787008,
    473209950721279316860076032, 17878107411321638850660401152, 196783324449516971712594313216, 17878200190309702782767071232, 473126449632021777964072960, 8640107558671545123471360,
    472992930431521456148971520, 473126449632021777964072960, 8508827553535451453194240, 8510329258564999821918208, 321524474196769019671871488, 3539001834403111655025147904,
    321526142757912962303787008, 8508827553535451453194240
  ]
def positiveScales : Array ℕ := #[
    41, 35, 40, 41, 45, 38,
    37, 45, 47, 45, 39, 33,
    35, 39, 31, 29, 38, 39,
    38, 31
  ]
def negativeArguments : Array ℕ := #[
    3
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    41851780968654100, 35611949087617408, 40077155430716353, 41851780968654100, 45852188163545897, 38055066512537056,
    37612610878249266, 45852180676655071, 47312522722648001, 45852188163545897, 39612356282510062, 33837323549485241,
    35611949087617408, 39612356282510062, 31815234631335544, 29815489227074474, 38055059025646213, 39515401071527376,
    38055066512537056, 31815234631335544
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 81522907 / 500000000000
noncomputable def negativeCeiling : ℝ := 18138457 / 1000000000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 17873154852012401020301737984, coefficient := (17873154852012401020301737984) }, { argument := 472992930431521456148971520, coefficient := (472992930431521456148971520) },
    { argument := 326486867770504009337536512, coefficient := (326486867770504009337536512) }, { argument := 17873154852012401020301737984, coefficient := (17873154852012401020301737984) },
    { argument := 17878200190309702782767071232, coefficient := (17878200190309702782767071232) }, { argument := 321526142757912962303787008, coefficient := (321526142757912962303787008) },
    { argument := 473209950721279316860076032, coefficient := (473209950721279316860076032) }, { argument := 17878107411321638850660401152, coefficient := (17878107411321638850660401152) },
    { argument := 196783324449516971712594313216, coefficient := (196783324449516971712594313216) }, { argument := 17878200190309702782767071232, coefficient := (17878200190309702782767071232) },
    { argument := 473126449632021777964072960, coefficient := (473126449632021777964072960) }, { argument := 8640107558671545123471360, coefficient := (8640107558671545123471360) },
    { argument := 472992930431521456148971520, coefficient := (472992930431521456148971520) }, { argument := 473126449632021777964072960, coefficient := (473126449632021777964072960) },
    { argument := 8508827553535451453194240, coefficient := (8508827553535451453194240) }, { argument := 8510329258564999821918208, coefficient := (8510329258564999821918208) },
    { argument := 321524474196769019671871488, coefficient := (321524474196769019671871488) }, { argument := 3539001834403111655025147904, coefficient := (3539001834403111655025147904) },
    { argument := 321526142757912962303787008, coefficient := (321526142757912962303787008) }, { argument := 8508827553535451453194240, coefficient := (8508827553535451453194240) },
    { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard16

end MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch2
