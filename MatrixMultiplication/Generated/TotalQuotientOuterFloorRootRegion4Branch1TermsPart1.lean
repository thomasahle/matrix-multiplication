/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.SignedDyadicLogCanonical
import MatrixMultiplication.RationalDyadicLog

/-!
# Bounded directed term shards, root orientation 4, branch 1

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
Every proof below checks at most 64 signed terms.  The untrusted producer supplies integer
arrays and rational endpoints only; the direction of every logarithm bound is proved by the
committed generic checkers of `SignedDyadicLogCertificate` and `RationalDyadicLog`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch1

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
def constantNumerator : ℤ := (383904291106194074834161360699392)
def positiveArguments : Array ℕ := #[
    357375921, 27028431, 51053703, 813856089, 2851203089191, 2475465425901,
    46794796755009, 187179232970681, 4950870593385, 2756497003525, 19660007621633, 5514590032885,
    5956498527525, 275529836357685, 137734878575385, 1498456957725, 19660007621633, 306183140259361,
    2940453789, 3618826593439551, 1281736267, 96938037, 2918912003, 2918912003,
    1281736267, 6537932051, 1281736267, 76546459592245, 2918912003, 96938037,
    1281736267, 96938037, 183105181, 2918912003, 20334094036887, 46794796755009,
    3539889074182949, 7079779872411553, 187176906856721, 21472370421361, 306183140259361, 85915848708123,
    819862407, 2940453789, 204965943, 5956499237595, 5956498527525, 5514590032885,
    85915848708123, 204965943, 1015594251020245, 89344129, 6757119, 203464361,
    203464361, 89344129, 455730137, 89344129, 10739575664417, 203464361,
    6757119, 89344129, 6757119, 12763447
  ]
def positiveCoefficients : Array ℕ := #[
    824052769099155361908129792, 124646637342729382473498624, 941774593256177556466434048, 938312186663323962508836864, 1605084646254774333936238592, 1393563146207036222170202112,
    52686257307184156950046703616, 52686270241140888164668276736, 1393546184970514526172610560, 1551769859740384849874124800, 5533800187430468132167221248, 1552219101075121080169922560,
    1676605284312156131976806400, 77554754271870244177166991360, 77537843478503049869257605120, 1687112549110259269396070400, 5533800187430468132167221248, 172365784547398313948984901632,
    3390112406640784145922392064, 2037218262216600413526307110912, 2955482610917606691316957184, 447047789886696810451304448, 3365276418313745434230652928, 3365276418313745434230652928,
    2955482610917606691316957184, 60301779658049991987542622208, 2955482610917606691316957184, 172367303448082655592851701760, 3365276418313745434230652928, 447047789886696810451304448,
    2955482610917606691316957184, 447047789886696810451304448, 3377694412477264790076522496, 3365276418313745434230652928, 5723538645465057371589967872, 52686257307184156950046703616,
    1992780389427902398573563609088, 1992780874703612987806232608768, 52685615498268170832865918976, 48351479714201329891989782528, 172365784547398313948984901632, 48366323028390331619135717376,
    945236999849031150424031232, 3390112406640784145922392064, 945238573586884938770153472, 1676605484179092844912312320, 1676605284312156131976806400, 1552219101075121080169922560,
    48366323028390331619135717376, 945238573586884938770153472, 571728736306799169884326461440, 824054141075745844056031232, 124646844868600211705954304, 938313748871962704786489344,
    938313748871962704786489344, 824054141075745844056031232, 16813474407831184112336502784, 824054141075745844056031232, 48366748960385648197822840832, 938313748871962704786489344,
    124646844868600211705954304, 824054141075745844056031232, 124646844868600211705954304, 941776161229423821778321408
  ]
def positiveScales : Array ℕ := #[
    28, 24, 25, 29, 41, 41,
    45, 47, 42, 41, 44, 42,
    42, 47, 46, 40, 44, 48,
    31, 51, 30, 26, 31, 31,
    30, 32, 30, 46, 31, 26,
    30, 26, 27, 31, 44, 45,
    51, 52, 47, 44, 48, 46,
    29, 31, 27, 42, 42, 42,
    46, 27, 49, 26, 22, 27,
    27, 26, 28, 26, 43, 27,
    22, 26, 22, 23
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    28412867191955748, 24687974430086738, 25605512269897735, 29600198470001323, 41374707943737445, 41170836938390959,
    45411413354945353, 47411413709112718, 42170819379056961, 41325973171783531, 44160329114506676, 42326390775234119,
    42437601643590794, 47969201880215575, 46968887266651507, 40446614782547526, 44160329114506676, 48121388172547923,
    31453391671843899, 51684443401761468, 30255452294231993, 26530559532366316, 31442783572277919, 31442783572277919,
    30255452294231993, 32606187237179314, 30255452294231993, 46121400885632690, 31442783572277919, 26530559532366316,
    30255452294231993, 26530559532366316, 27448097372174386, 31442783572277919, 44208965948082669, 45411413354945353,
    51652625576093698, 52652625927414285, 47411395780339993, 44287546698433975, 48121388172547923, 46287989520237857,
    29610806569567184, 31453391671843899, 27610808971527653, 42437601815573445, 42437601643590794, 42326390775234119,
    46287989520237857, 27610808971527653, 49851245556650378, 26412869593916217, 22687976832047207, 27600200871961791,
    27600200871961791, 26412869593916217, 28763604536845237, 26412869593916217, 43288002225095973, 27600200871961791,
    22687976832047207, 26412869593916217, 22687976832047207, 23605514671858204
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
noncomputable def positiveFloor : ℝ := 4783212279 / 1000000000000
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
    { argument := 824052769099155361908129792, coefficient := (824052769099155361908129792) }, { argument := 124646637342729382473498624, coefficient := (124646637342729382473498624) },
    { argument := 941774593256177556466434048, coefficient := (941774593256177556466434048) }, { argument := 938312186663323962508836864, coefficient := (938312186663323962508836864) },
    { argument := 1605084646254774333936238592, coefficient := (1605084646254774333936238592) }, { argument := 1393563146207036222170202112, coefficient := (1393563146207036222170202112) },
    { argument := 52686257307184156950046703616, coefficient := (52686257307184156950046703616) }, { argument := 52686270241140888164668276736, coefficient := (52686270241140888164668276736) },
    { argument := 1393546184970514526172610560, coefficient := (1393546184970514526172610560) }, { argument := 1551769859740384849874124800, coefficient := (1551769859740384849874124800) },
    { argument := 5533800187430468132167221248, coefficient := (5533800187430468132167221248) }, { argument := 1552219101075121080169922560, coefficient := (1552219101075121080169922560) },
    { argument := 1676605284312156131976806400, coefficient := (1676605284312156131976806400) }, { argument := 77554754271870244177166991360, coefficient := (77554754271870244177166991360) },
    { argument := 77537843478503049869257605120, coefficient := (77537843478503049869257605120) }, { argument := 1687112549110259269396070400, coefficient := (1687112549110259269396070400) },
    { argument := 5533800187430468132167221248, coefficient := (5533800187430468132167221248) }, { argument := 172365784547398313948984901632, coefficient := (172365784547398313948984901632) },
    { argument := 3390112406640784145922392064, coefficient := (3390112406640784145922392064) }, { argument := 2037218262216600413526307110912, coefficient := (2037218262216600413526307110912) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) }, { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 60301779658049991987542622208, coefficient := (60301779658049991987542622208) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 172367303448082655592851701760, coefficient := (172367303448082655592851701760) },
    { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 3377694412477264790076522496, coefficient := (3377694412477264790076522496) }, { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) },
    { argument := 5723538645465057371589967872, coefficient := (5723538645465057371589967872) }, { argument := 52686257307184156950046703616, coefficient := (52686257307184156950046703616) },
    { argument := 1992780389427902398573563609088, coefficient := (1992780389427902398573563609088) }, { argument := 1992780874703612987806232608768, coefficient := (1992780874703612987806232608768) },
    { argument := 52685615498268170832865918976, coefficient := (52685615498268170832865918976) }, { argument := 48351479714201329891989782528, coefficient := (48351479714201329891989782528) },
    { argument := 172365784547398313948984901632, coefficient := (172365784547398313948984901632) }, { argument := 48366323028390331619135717376, coefficient := (48366323028390331619135717376) },
    { argument := 945236999849031150424031232, coefficient := (945236999849031150424031232) }, { argument := 3390112406640784145922392064, coefficient := (3390112406640784145922392064) },
    { argument := 945238573586884938770153472, coefficient := (945238573586884938770153472) }, { argument := 1676605484179092844912312320, coefficient := (1676605484179092844912312320) },
    { argument := 1676605284312156131976806400, coefficient := (1676605284312156131976806400) }, { argument := 1552219101075121080169922560, coefficient := (1552219101075121080169922560) },
    { argument := 48366323028390331619135717376, coefficient := (48366323028390331619135717376) }, { argument := 945238573586884938770153472, coefficient := (945238573586884938770153472) },
    { argument := 571728736306799169884326461440, coefficient := (571728736306799169884326461440) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) },
    { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 16813474407831184112336502784, coefficient := (16813474407831184112336502784) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 48366748960385648197822840832, coefficient := (48366748960385648197822840832) }, { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 941776161229423821778321408, coefficient := (941776161229423821778321408) }] }

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
def constantNumerator : ℤ := (396909439360769694686801953816576)
def positiveArguments : Array ℕ := #[
    203464361, 5704063076891, 187179232970681, 7079779872411553, 7079781596457723, 187176952806827,
    253819157275195, 3618826593439551, 1015594251020245, 357375921, 1281736267, 89344129,
    275529869203403, 275529836357685, 27028431, 96938037, 6757119, 813856089,
    2918912003, 203464361, 813856089, 2918912003, 203464361, 357375921,
    1281736267, 89344129, 1822917513, 6537932051, 455730137, 357375921,
    1281736267, 89344129, 4950870593385, 187176906856721, 187176952806827, 4950810335707,
    21472559512457, 76546459592245, 10739575664417, 137734894994663, 137734878575385, 813856089,
    2918912003, 203464361, 27028431, 96938037, 6757119, 357375921,
    1281736267, 89344129, 27028431, 96938037, 6757119, 51053703,
    183105181, 12763447, 813856089, 2918912003, 203464361, 2851203089191,
    20334094036887, 5704063076891, 1498457136355, 1498456957725
  ]
def positiveCoefficients : Array ℕ := #[
    938313748871962704786489344, 1605551021724007029587050496, 52686270241140888164668276736, 1992780874703612987806232608768, 1992781359979468536651907596288, 52685628432073187035040448512,
    571549931062030760423047823360, 2037218262216600413526307110912, 571728736306799169884326461440, 824052769099155361908129792, 2955482610917606691316957184, 824054141075745844056031232,
    77554763517117953271941562368, 77554754271870244177166991360, 124646637342729382473498624, 447047789886696810451304448, 124646844868600211705954304, 938312186663323962508836864,
    3365276418313745434230652928, 938313748871962704786489344, 938312186663323962508836864, 3365276418313745434230652928, 938313748871962704786489344, 824052769099155361908129792,
    2955482610917606691316957184, 824054141075745844056031232, 16813446414897052258091925504, 60301779658049991987542622208, 16813474407831184112336502784, 824052769099155361908129792,
    2955482610917606691316957184, 824054141075745844056031232, 1393546184970514526172610560, 52685615498268170832865918976, 52685628432073187035040448512, 1393529223942002837964193792,
    48351905509496072231333134336, 172367303448082655592851701760, 48366748960385648197822840832, 77537852721734835180830457856, 77537843478503049869257605120, 938312186663323962508836864,
    3365276418313745434230652928, 938313748871962704786489344, 124646637342729382473498624, 447047789886696810451304448, 124646844868600211705954304, 824052769099155361908129792,
    2955482610917606691316957184, 824054141075745844056031232, 124646637342729382473498624, 447047789886696810451304448, 124646844868600211705954304, 941774593256177556466434048,
    3377694412477264790076522496, 941776161229423821778321408, 938312186663323962508836864, 3365276418313745434230652928, 938313748871962704786489344, 1605084646254774333936238592,
    5723538645465057371589967872, 1605551021724007029587050496, 1687112750229759628693995520, 1687112549110259269396070400
  ]
def positiveScales : Array ℕ := #[
    27, 42, 47, 52, 52, 47,
    47, 51, 49, 28, 30, 26,
    47, 47, 24, 26, 22, 29,
    31, 27, 29, 31, 27, 28,
    30, 26, 30, 32, 28, 28,
    30, 26, 42, 47, 47, 42,
    44, 46, 43, 46, 46, 29,
    31, 27, 24, 26, 22, 28,
    30, 26, 24, 26, 22, 25,
    27, 23, 29, 31, 27, 41,
    44, 42, 40, 40
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    27600200871961791, 42375127074184476, 47411413709112718, 52652625927414285, 52652626278734892, 47411396134507518,
    47850794290570040, 51684443401761468, 49851245556650378, 28412867191955748, 30255452294231993, 26412869593916217,
    47969202052198223, 47969201880215575, 24687974430086738, 26530559532366316, 22687976832047207, 29600198470001323,
    31442783572277919, 27600200871961791, 29600198470001323, 31442783572277919, 27600200871961791, 28412867191955748,
    30255452294231993, 26412869593916217, 30763602134884769, 32606187237179314, 28763604536845237, 28412867191955748,
    30255452294231993, 26412869593916217, 42170819379056961, 47411395780339993, 47411396134507518, 42170801819724591,
    44287559403113522, 46121400885632690, 43288002225095973, 46968887438634155, 46968887266651507, 29600198470001323,
    31442783572277919, 27600200871961791, 24687974430086738, 26530559532366316, 22687976832047207, 28412867191955748,
    30255452294231993, 26412869593916217, 24687974430086738, 26530559532366316, 22687976832047207, 25605512269897735,
    27448097372174386, 23605514671858204, 29600198470001323, 31442783572277919, 27600200871961791, 41374707943737445,
    44208965948082669, 42375127074184476, 40446614954530177, 40446614782547526
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
noncomputable def positiveFloor : ℝ := 155340261 / 31250000000
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
    { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) }, { argument := 1605551021724007029587050496, coefficient := (1605551021724007029587050496) },
    { argument := 52686270241140888164668276736, coefficient := (52686270241140888164668276736) }, { argument := 1992780874703612987806232608768, coefficient := (1992780874703612987806232608768) },
    { argument := 1992781359979468536651907596288, coefficient := (1992781359979468536651907596288) }, { argument := 52685628432073187035040448512, coefficient := (52685628432073187035040448512) },
    { argument := 571549931062030760423047823360, coefficient := (571549931062030760423047823360) }, { argument := 2037218262216600413526307110912, coefficient := (2037218262216600413526307110912) },
    { argument := 571728736306799169884326461440, coefficient := (571728736306799169884326461440) }, { argument := 824052769099155361908129792, coefficient := (824052769099155361908129792) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 77554763517117953271941562368, coefficient := (77554763517117953271941562368) }, { argument := 77554754271870244177166991360, coefficient := (77554754271870244177166991360) },
    { argument := 124646637342729382473498624, coefficient := (124646637342729382473498624) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 938312186663323962508836864, coefficient := (938312186663323962508836864) },
    { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) }, { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) },
    { argument := 938312186663323962508836864, coefficient := (938312186663323962508836864) }, { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) },
    { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) }, { argument := 824052769099155361908129792, coefficient := (824052769099155361908129792) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 16813446414897052258091925504, coefficient := (16813446414897052258091925504) }, { argument := 60301779658049991987542622208, coefficient := (60301779658049991987542622208) },
    { argument := 16813474407831184112336502784, coefficient := (16813474407831184112336502784) }, { argument := 824052769099155361908129792, coefficient := (824052769099155361908129792) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 1393546184970514526172610560, coefficient := (1393546184970514526172610560) }, { argument := 52685615498268170832865918976, coefficient := (52685615498268170832865918976) },
    { argument := 52685628432073187035040448512, coefficient := (52685628432073187035040448512) }, { argument := 1393529223942002837964193792, coefficient := (1393529223942002837964193792) },
    { argument := 48351905509496072231333134336, coefficient := (48351905509496072231333134336) }, { argument := 172367303448082655592851701760, coefficient := (172367303448082655592851701760) },
    { argument := 48366748960385648197822840832, coefficient := (48366748960385648197822840832) }, { argument := 77537852721734835180830457856, coefficient := (77537852721734835180830457856) },
    { argument := 77537843478503049869257605120, coefficient := (77537843478503049869257605120) }, { argument := 938312186663323962508836864, coefficient := (938312186663323962508836864) },
    { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) }, { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) },
    { argument := 124646637342729382473498624, coefficient := (124646637342729382473498624) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 824052769099155361908129792, coefficient := (824052769099155361908129792) },
    { argument := 2955482610917606691316957184, coefficient := (2955482610917606691316957184) }, { argument := 824054141075745844056031232, coefficient := (824054141075745844056031232) },
    { argument := 124646637342729382473498624, coefficient := (124646637342729382473498624) }, { argument := 447047789886696810451304448, coefficient := (447047789886696810451304448) },
    { argument := 124646844868600211705954304, coefficient := (124646844868600211705954304) }, { argument := 941774593256177556466434048, coefficient := (941774593256177556466434048) },
    { argument := 3377694412477264790076522496, coefficient := (3377694412477264790076522496) }, { argument := 941776161229423821778321408, coefficient := (941776161229423821778321408) },
    { argument := 938312186663323962508836864, coefficient := (938312186663323962508836864) }, { argument := 3365276418313745434230652928, coefficient := (3365276418313745434230652928) },
    { argument := 938313748871962704786489344, coefficient := (938313748871962704786489344) }, { argument := 1605084646254774333936238592, coefficient := (1605084646254774333936238592) },
    { argument := 5723538645465057371589967872, coefficient := (5723538645465057371589967872) }, { argument := 1605551021724007029587050496, coefficient := (1605551021724007029587050496) },
    { argument := 1687112750229759628693995520, coefficient := (1687112750229759628693995520) }, { argument := 1687112549110259269396070400, coefficient := (1687112549110259269396070400) }] }

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
def constantNumerator : ℤ := (-1494852185634509315543635966558208)
def positiveArguments : Array ℕ := #[
    3227158444185, 149278713646569, 74623081731549, 811845751665, 233808556321, 865453131253,
    63195405, 10051802057893, 27546715, 2083365, 62732435, 62732435,
    27546715, 140511395, 27546715, 1730920822435, 62732435, 2083365,
    27546715, 2083365, 3935245, 62732435, 241146253187, 233808556321,
    2192886716717, 17543098609961, 467611493165, 11414024830455, 527978707488167, 263931790936307,
    2871389096095, 2192886716717, 130788581327075, 1113447153, 1522845259199301, 485348759,
    36707049, 1105290031, 1105290031, 485348759, 2475686527, 485348759,
    65394844431829, 1105290031, 36707049, 485348759, 36707049, 69335537,
    1105290031, 1131288881013, 865453131253, 130788581327075, 32697153451051, 3461770434205,
    63195405, 1113447153, 4453791069, 126389445, 3227158444185, 11414024830455,
    201769585815, 201769585815, 9333258575431
  ]
def positiveCoefficients : Array ℕ := #[
    908364347918569725870735360, 42018222447064695282560139264, 42009060384930267977679372288, 914057056170203558140968960, 131622515890411153393713152, 3897654399417639765947711488,
    145718682833678120842690560, 45269292002328899661152124928, 127036800419104002785935360, 19215650483561950001233920, 144651146695702456953733120, 144651146695702456953733120,
    127036800419104002785935360, 2591977743004911922388664320, 127036800419104002785935360, 3897687185463049236386938880, 144651146695702456953733120, 19215650483561950001233920,
    127036800419104002785935360, 19215650483561950001233920, 145184914764690288898211840, 144651146695702456953733120, 135753271999345560433721344, 131622515890411153393713152,
    4937941900136195810777890816, 4937943272671514121696444416, 131620934148253452326666240, 3212762373327170423991828480, 148612794393954062957702807552, 148580389413997482346528374784,
    3232896715802286832777953280, 4937941900136195810777890816, 147254851532232695307095244800, 5134868667747880598935437312, 1714571335468224594853257805824, 4476552171882767701636022272,
    677125538604116122936541184, 5097250582269874147661185024, 5097250582269874147661185024, 4476552171882767701636022272, 91336711540599663693884555264, 4476552171882767701636022272,
    147256098507568319805198958592, 5097250582269874147661185024, 677125538604116122936541184, 4476552171882767701636022272, 677125538604116122936541184, 5116059625008877373298311168,
    5097250582269874147661185024, 5094872182978532187410792448, 3897654399417639765947711488, 147254851532232695307095244800, 147254888098229210922977591296, 3897607009381959535081553920,
    145718682833678120842690560, 5134868667747880598935437312, 5134871500476017417958457344, 145717109095824332496568320, 908364347918569725870735360, 3212762373327170423991828480,
    908689431491133315471114240, 908689431491133315471114240, 42033259842463537933399883776
  ]
def positiveScales : Array ℕ := #[
    41, 47, 46, 39, 37, 39,
    25, 43, 24, 20, 25, 25,
    24, 27, 24, 40, 25, 20,
    24, 20, 21, 25, 37, 37,
    40, 43, 38, 43, 48, 47,
    41, 40, 46, 30, 50, 28,
    25, 30, 30, 28, 31, 28,
    45, 30, 25, 28, 25, 26,
    30, 40, 39, 46, 44, 41,
    25, 30, 32, 26, 41, 43,
    37, 37, 43
  ]
def negativeArguments : Array ℕ := #[
    53
  ]
def negativeCoefficients : Array ℕ := #[
    16796370453024039569831317471232
  ]
def negativeScales : Array ℕ := #[
    5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    41553401550383365, 47085001787894516, 46084687174325862, 39562414689340070, 37766536770599514, 39654664736095777,
    25913316326311258, 43192519400305845, 24715376949034912, 20990484185922282, 25902708226803907, 25902708226803907,
    24715376949034912, 27066111891989075, 24715376949034912, 40654676871616615, 25902708226803907, 20990484185922282,
    24715376949034912, 20990484185922282, 21908022026672289, 25902708226803907, 37811117438092132, 37766536770599514,
    40995968422409308, 43995968823416371, 38766519433252161, 43375872840153627, 48907473077356260, 47907158463789323,
    41384885979110360, 40995968422409308, 46894229918083658, 30052385939804717, 50435690776082691, 28854446562076158,
    25129553800327177, 30041777840238737, 30041777840238737, 28854446562076158, 31205181505140547, 28854446562076158,
    45894242134981704, 30041777840238737, 25129553800327177, 28854446562076158, 25129553800327177, 26047091640135204,
    30041777840238737, 40041104515357514, 39654664736095777, 46894229918083658, 44894230276330429, 41654647194831699,
    25913316326311258, 30052385939804717, 32052386735689086, 26913300745357603, 41553401550383365, 43375872840153627,
    37553917766764332, 37553917766764332, 43085518004275484
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5727920454700926
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
noncomputable def positiveFloor : ℝ := 1715782889 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1158064973 / 1000000000000

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
    { argument := 16796370453024039569831317471232, coefficient := (-16796370453024039569831317471232) }, { argument := 908364347918569725870735360, coefficient := (908364347918569725870735360) },
    { argument := 42018222447064695282560139264, coefficient := (42018222447064695282560139264) }, { argument := 42009060384930267977679372288, coefficient := (42009060384930267977679372288) },
    { argument := 914057056170203558140968960, coefficient := (914057056170203558140968960) }, { argument := 131622515890411153393713152, coefficient := (131622515890411153393713152) },
    { argument := 3897654399417639765947711488, coefficient := (3897654399417639765947711488) }, { argument := 145718682833678120842690560, coefficient := (145718682833678120842690560) },
    { argument := 45269292002328899661152124928, coefficient := (45269292002328899661152124928) }, { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) },
    { argument := 2591977743004911922388664320, coefficient := (2591977743004911922388664320) }, { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) },
    { argument := 3897687185463049236386938880, coefficient := (3897687185463049236386938880) }, { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 145184914764690288898211840, coefficient := (145184914764690288898211840) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 135753271999345560433721344, coefficient := (135753271999345560433721344) },
    { argument := 131622515890411153393713152, coefficient := (131622515890411153393713152) }, { argument := 4937941900136195810777890816, coefficient := (4937941900136195810777890816) },
    { argument := 4937943272671514121696444416, coefficient := (4937943272671514121696444416) }, { argument := 131620934148253452326666240, coefficient := (131620934148253452326666240) },
    { argument := 3212762373327170423991828480, coefficient := (3212762373327170423991828480) }, { argument := 148612794393954062957702807552, coefficient := (148612794393954062957702807552) },
    { argument := 148580389413997482346528374784, coefficient := (148580389413997482346528374784) }, { argument := 3232896715802286832777953280, coefficient := (3232896715802286832777953280) },
    { argument := 4937941900136195810777890816, coefficient := (4937941900136195810777890816) }, { argument := 147254851532232695307095244800, coefficient := (147254851532232695307095244800) },
    { argument := 5134868667747880598935437312, coefficient := (5134868667747880598935437312) }, { argument := 1714571335468224594853257805824, coefficient := (1714571335468224594853257805824) },
    { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) }, { argument := 91336711540599663693884555264, coefficient := (91336711540599663693884555264) },
    { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) }, { argument := 147256098507568319805198958592, coefficient := (147256098507568319805198958592) },
    { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 5116059625008877373298311168, coefficient := (5116059625008877373298311168) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 5094872182978532187410792448, coefficient := (5094872182978532187410792448) }, { argument := 3897654399417639765947711488, coefficient := (3897654399417639765947711488) },
    { argument := 147254851532232695307095244800, coefficient := (147254851532232695307095244800) }, { argument := 147254888098229210922977591296, coefficient := (147254888098229210922977591296) },
    { argument := 3897607009381959535081553920, coefficient := (3897607009381959535081553920) }, { argument := 145718682833678120842690560, coefficient := (145718682833678120842690560) },
    { argument := 5134868667747880598935437312, coefficient := (5134868667747880598935437312) }, { argument := 5134871500476017417958457344, coefficient := (5134871500476017417958457344) },
    { argument := 145717109095824332496568320, coefficient := (145717109095824332496568320) }, { argument := 908364347918569725870735360, coefficient := (908364347918569725870735360) },
    { argument := 3212762373327170423991828480, coefficient := (3212762373327170423991828480) }, { argument := 908689431491133315471114240, coefficient := (908689431491133315471114240) },
    { argument := 908689431491133315471114240, coefficient := (908689431491133315471114240) }, { argument := 42033259842463537933399883776, coefficient := (42033259842463537933399883776) }] }

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
def constantNumerator : ℤ := (327634788897638904802901273608192)
def positiveArguments : Array ℕ := #[
    4665611730451, 50758518335, 17543098609961, 32697153451051, 4453791069, 190355702670347,
    1941396107, 146828277, 4421162563, 4421162563, 1941396107, 9902751571,
    1941396107, 130789721341031, 4421162563, 146828277, 1941396107, 146828277,
    277342301, 4421162563, 18100627097899, 10051802057893, 1522845259199301, 190355702670347,
    40206717336015, 27546715, 485348759, 1941396107, 55092835, 149278713646569,
    527978707488167, 9333258575431, 2083365, 36707049, 146828277, 4166685,
    62732435, 1105290031, 4421162563, 125463515, 62732435, 1105290031,
    4421162563, 125463515, 27546715, 485348759, 1941396107, 55092835,
    140511395, 2475686527, 9902751571, 281019755, 27546715, 485348759,
    1941396107, 55092835, 467611493165, 3461770434205, 126389445, 40206717336015,
    55092835, 4166685, 125463515, 125463515
  ]
def positiveCoefficients : Array ℕ := #[
    42024094501429077250924347392, 914384177037537956216176640, 4937943272671514121696444416, 147254888098229210922977591296, 5134871500476017417958457344, 1714571743228047359154243764224,
    4476554641440630569502244864, 677125912150683615554961408, 5097253394245423883760959488, 5097253394245423883760959488, 4476554641440630569502244864, 91336761927881101031524794368,
    4476554641440630569502244864, 147256135073839554998350905344, 5097253394245423883760959488, 677125912150683615554961408, 4476554641440630569502244864, 677125912150683615554961408,
    5116062447360720650859708416, 5097253394245423883760959488, 5094873590829389926308511744, 45269292002328899661152124928, 1714571335468224594853257805824, 1714571743228047359154243764224,
    45268739303067003903132303360, 127036800419104002785935360, 4476552171882767701636022272, 4476554641440630569502244864, 127035428442513520638033920, 42018222447064695282560139264,
    148612794393954062957702807552, 42033259842463537933399883776, 19215650483561950001233920, 677125538604116122936541184, 677125912150683615554961408, 19215442957691120768778240,
    144651146695702456953733120, 5097250582269874147661185024, 5097253394245423883760959488, 144649584487063714676080640, 144651146695702456953733120, 5097250582269874147661185024,
    5097253394245423883760959488, 144649584487063714676080640, 127036800419104002785935360, 4476552171882767701636022272, 4476554641440630569502244864, 127035428442513520638033920,
    2591977743004911922388664320, 91336711540599663693884555264, 91336761927881101031524794368, 2591949750070780068144087040, 127036800419104002785935360, 4476552171882767701636022272,
    4476554641440630569502244864, 127035428442513520638033920, 131620934148253452326666240, 3897607009381959535081553920, 145717109095824332496568320, 45268739303067003903132303360,
    127035428442513520638033920, 19215442957691120768778240, 144649584487063714676080640, 144649584487063714676080640
  ]
def positiveScales : Array ℕ := #[
    42, 35, 43, 44, 32, 47,
    30, 27, 32, 32, 30, 33,
    30, 46, 32, 27, 30, 27,
    28, 32, 44, 43, 50, 47,
    45, 24, 28, 30, 25, 47,
    48, 43, 20, 25, 27, 21,
    25, 30, 32, 26, 25, 30,
    32, 26, 24, 28, 30, 25,
    27, 31, 33, 28, 24, 28,
    30, 25, 38, 41, 26, 45,
    25, 21, 26, 26
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    42085203390706830, 35562930905721036, 43995968823416371, 44894230276330429, 32052386735689086, 47435691119184779,
    30854447357960525, 27129554596211546, 32041778636123105, 32041778636123105, 30854447357960525, 33205182301024916,
    30854447357960525, 46894242493228132, 32041778636123105, 27129554596211546, 30854447357960525, 27129554596211546,
    28047092436019573, 32041778636123105, 44041104914013083, 43192519400305845, 50435690776082691, 47435691119184779,
    45192501786128184, 24715376949034912, 28854446562076158, 30854447357960525, 25715361368081165, 47085001787894516,
    48907473077356260, 43085518004275484, 20990484185922282, 25129553800327177, 27129554596211546, 21990468604968848,
    25902708226803907, 30041777840238737, 32041778636123105, 26902692645850238, 25902708226803907, 30041777840238737,
    32041778636123105, 26902692645850238, 24715376949034912, 28854446562076158, 30854447357960525, 25715361368081165,
    27066111891989075, 31205181505140547, 33205182301024916, 28066096311035326, 24715376949034912, 28854446562076158,
    30854447357960525, 25715361368081165, 38766519433252161, 41654647194831699, 26913300745357603, 45192501786128184,
    25715361368081165, 21990468604968848, 26902692645850238, 26902692645850238
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
noncomputable def positiveFloor : ℝ := 3542738777 / 1000000000000
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
    { argument := 42024094501429077250924347392, coefficient := (42024094501429077250924347392) }, { argument := 914384177037537956216176640, coefficient := (914384177037537956216176640) },
    { argument := 4937943272671514121696444416, coefficient := (4937943272671514121696444416) }, { argument := 147254888098229210922977591296, coefficient := (147254888098229210922977591296) },
    { argument := 5134871500476017417958457344, coefficient := (5134871500476017417958457344) }, { argument := 1714571743228047359154243764224, coefficient := (1714571743228047359154243764224) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 91336761927881101031524794368, coefficient := (91336761927881101031524794368) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 147256135073839554998350905344, coefficient := (147256135073839554998350905344) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) },
    { argument := 5116062447360720650859708416, coefficient := (5116062447360720650859708416) }, { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) },
    { argument := 5094873590829389926308511744, coefficient := (5094873590829389926308511744) }, { argument := 45269292002328899661152124928, coefficient := (45269292002328899661152124928) },
    { argument := 1714571335468224594853257805824, coefficient := (1714571335468224594853257805824) }, { argument := 1714571743228047359154243764224, coefficient := (1714571743228047359154243764224) },
    { argument := 45268739303067003903132303360, coefficient := (45268739303067003903132303360) }, { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) },
    { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) }, { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) },
    { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) }, { argument := 42018222447064695282560139264, coefficient := (42018222447064695282560139264) },
    { argument := 148612794393954062957702807552, coefficient := (148612794393954062957702807552) }, { argument := 42033259842463537933399883776, coefficient := (42033259842463537933399883776) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) },
    { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) }, { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) },
    { argument := 2591977743004911922388664320, coefficient := (2591977743004911922388664320) }, { argument := 91336711540599663693884555264, coefficient := (91336711540599663693884555264) },
    { argument := 91336761927881101031524794368, coefficient := (91336761927881101031524794368) }, { argument := 2591949750070780068144087040, coefficient := (2591949750070780068144087040) },
    { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) }, { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) },
    { argument := 131620934148253452326666240, coefficient := (131620934148253452326666240) }, { argument := 3897607009381959535081553920, coefficient := (3897607009381959535081553920) },
    { argument := 145717109095824332496568320, coefficient := (145717109095824332496568320) }, { argument := 45268739303067003903132303360, coefficient := (45268739303067003903132303360) },
    { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) }] }

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
def constantNumerator : ℤ := (-915510417225145135429773487505408)
def positiveArguments : Array ℕ := #[
    55092835, 281019755, 55092835, 3461799553705, 125463515, 4166685,
    55092835, 4166685, 7870405, 125463515, 482286706815, 1730920822435,
    65394844431829, 130789721341031, 3461799553705, 74623081731549, 263931790936307, 4665611730451,
    62732435, 1105290031, 4421162563, 125463515, 2083365, 36707049,
    146828277, 4166685, 27546715, 485348759, 1941396107, 55092835,
    2083365, 36707049, 146828277, 4166685, 3935245, 69335537,
    277342301, 7870405, 62732435, 1105290031, 4421162563, 125463515,
    241146253187, 1131288881013, 18100627097899, 482286706815, 811845751665, 2871389096095,
    50758518335, 143655326805, 6645066477157, 3321808761097, 36138903245, 32336218945,
    534456138137, 6440390195975, 133615248841, 33595022647, 1453211155215, 67221208892991,
    33603275663211, 365579602935, 534456138137
  ]
def positiveCoefficients : Array ℕ := #[
    127035428442513520638033920, 2591949750070780068144087040, 127035428442513520638033920, 3897639795024296838871121920, 144649584487063714676080640, 19215442957691120768778240,
    127035428442513520638033920, 19215442957691120768778240, 145183346791444023586324480, 144649584487063714676080640, 135751639568611103358320640, 3897687185463049236386938880,
    147256098507568319805198958592, 147256135073839554998350905344, 3897639795024296838871121920, 42009060384930267977679372288, 148580389413997482346528374784, 42024094501429077250924347392,
    144651146695702456953733120, 5097250582269874147661185024, 5097253394245423883760959488, 144649584487063714676080640, 19215650483561950001233920, 677125538604116122936541184,
    677125912150683615554961408, 19215442957691120768778240, 127036800419104002785935360, 4476552171882767701636022272, 4476554641440630569502244864, 127035428442513520638033920,
    19215650483561950001233920, 677125538604116122936541184, 677125912150683615554961408, 19215442957691120768778240, 145184914764690288898211840, 5116059625008877373298311168,
    5116062447360720650859708416, 145183346791444023586324480, 144651146695702456953733120, 5097250582269874147661185024, 5097253394245423883760959488, 144649584487063714676080640,
    135753271999345560433721344, 5094872182978532187410792448, 5094873590829389926308511744, 135751639568611103358320640, 914057056170203558140968960, 3232896715802286832777953280,
    914384177037537956216176640, 80870759533598103211868160, 3740839863797054971244969984, 3740024174668124542392598528, 81377575593880204355829760, 9101836474454548330577920,
    300872058069958442031775744, 3625617360839200713421619200, 300874792445671848770797568, 9456158217158285886226432, 3272340608558461012483768320, 151368705660934269762187296768,
    151335699755265116442414022656, 3292848327104639771628011520, 300872058069958442031775744
  ]
def positiveScales : Array ℕ := #[
    25, 28, 25, 41, 26, 21,
    25, 21, 22, 26, 38, 40,
    45, 46, 41, 46, 47, 42,
    25, 30, 32, 26, 20, 25,
    27, 21, 24, 28, 30, 25,
    20, 25, 27, 21, 21, 26,
    28, 22, 25, 30, 32, 26,
    37, 40, 44, 38, 39, 41,
    35, 37, 42, 41, 35, 34,
    38, 42, 36, 34, 40, 45,
    44, 38, 38
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
    25715361368081165, 28066096311035326, 25715361368081165, 41654659330350894, 26902692645850238, 21990468604968848,
    25715361368081165, 21990468604968848, 22908006445718626, 26902692645850238, 38811100089605070, 40654676871616615,
    45894242134981704, 46894242493228132, 41654659330350894, 46084687174325862, 47907158463789323, 42085203390706830,
    25902708226803907, 30041777840238737, 32041778636123105, 26902692645850238, 20990484185922282, 25129553800327177,
    27129554596211546, 21990468604968848, 24715376949034912, 28854446562076158, 30854447357960525, 25715361368081165,
    20990484185922282, 25129553800327177, 27129554596211546, 21990468604968848, 21908022026672289, 26047091640135204,
    28047092436019573, 22908006445718626, 25902708226803907, 30041777840238737, 32041778636123105, 26902692645850238,
    37811117438092132, 40041104515357514, 44041104914013083, 38811100089605070, 39562414689340070, 41384885979110360,
    35562930905721036, 37063820533413007, 42595420770923755, 41595106157355104, 35072833672369740, 34912431943730532,
    38959280596401546, 42550285236420590, 36959293707796243, 34967528450824795, 40402381484047545, 45933981721068665,
    44933667107502652, 38411394623004277, 38959280596401546
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
noncomputable def positiveFloor : ℝ := 249829469 / 500000000000
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
    { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) }, { argument := 2591949750070780068144087040, coefficient := (2591949750070780068144087040) },
    { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) }, { argument := 3897639795024296838871121920, coefficient := (3897639795024296838871121920) },
    { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 145183346791444023586324480, coefficient := (145183346791444023586324480) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) },
    { argument := 135751639568611103358320640, coefficient := (135751639568611103358320640) }, { argument := 3897687185463049236386938880, coefficient := (3897687185463049236386938880) },
    { argument := 147256098507568319805198958592, coefficient := (147256098507568319805198958592) }, { argument := 147256135073839554998350905344, coefficient := (147256135073839554998350905344) },
    { argument := 3897639795024296838871121920, coefficient := (3897639795024296838871121920) }, { argument := 42009060384930267977679372288, coefficient := (42009060384930267977679372288) },
    { argument := 148580389413997482346528374784, coefficient := (148580389413997482346528374784) }, { argument := 42024094501429077250924347392, coefficient := (42024094501429077250924347392) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 127036800419104002785935360, coefficient := (127036800419104002785935360) }, { argument := 4476552171882767701636022272, coefficient := (4476552171882767701636022272) },
    { argument := 4476554641440630569502244864, coefficient := (4476554641440630569502244864) }, { argument := 127035428442513520638033920, coefficient := (127035428442513520638033920) },
    { argument := 19215650483561950001233920, coefficient := (19215650483561950001233920) }, { argument := 677125538604116122936541184, coefficient := (677125538604116122936541184) },
    { argument := 677125912150683615554961408, coefficient := (677125912150683615554961408) }, { argument := 19215442957691120768778240, coefficient := (19215442957691120768778240) },
    { argument := 145184914764690288898211840, coefficient := (145184914764690288898211840) }, { argument := 5116059625008877373298311168, coefficient := (5116059625008877373298311168) },
    { argument := 5116062447360720650859708416, coefficient := (5116062447360720650859708416) }, { argument := 145183346791444023586324480, coefficient := (145183346791444023586324480) },
    { argument := 144651146695702456953733120, coefficient := (144651146695702456953733120) }, { argument := 5097250582269874147661185024, coefficient := (5097250582269874147661185024) },
    { argument := 5097253394245423883760959488, coefficient := (5097253394245423883760959488) }, { argument := 144649584487063714676080640, coefficient := (144649584487063714676080640) },
    { argument := 135753271999345560433721344, coefficient := (135753271999345560433721344) }, { argument := 5094872182978532187410792448, coefficient := (5094872182978532187410792448) },
    { argument := 5094873590829389926308511744, coefficient := (5094873590829389926308511744) }, { argument := 135751639568611103358320640, coefficient := (135751639568611103358320640) },
    { argument := 914057056170203558140968960, coefficient := (914057056170203558140968960) }, { argument := 3232896715802286832777953280, coefficient := (3232896715802286832777953280) },
    { argument := 914384177037537956216176640, coefficient := (914384177037537956216176640) }, { argument := 9824292151768777861599449841664, coefficient := (-9824292151768777861599449841664) },
    { argument := 80870759533598103211868160, coefficient := (80870759533598103211868160) }, { argument := 3740839863797054971244969984, coefficient := (3740839863797054971244969984) },
    { argument := 3740024174668124542392598528, coefficient := (3740024174668124542392598528) }, { argument := 81377575593880204355829760, coefficient := (81377575593880204355829760) },
    { argument := 9101836474454548330577920, coefficient := (9101836474454548330577920) }, { argument := 300872058069958442031775744, coefficient := (300872058069958442031775744) },
    { argument := 3625617360839200713421619200, coefficient := (3625617360839200713421619200) }, { argument := 300874792445671848770797568, coefficient := (300874792445671848770797568) },
    { argument := 9456158217158285886226432, coefficient := (9456158217158285886226432) }, { argument := 3272340608558461012483768320, coefficient := (3272340608558461012483768320) },
    { argument := 151368705660934269762187296768, coefficient := (151368705660934269762187296768) }, { argument := 151335699755265116442414022656, coefficient := (151335699755265116442414022656) },
    { argument := 3292848327104639771628011520, coefficient := (3292848327104639771628011520) }, { argument := 300872058069958442031775744, coefficient := (300872058069958442031775744) }] }

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
def constantNumerator : ℤ := (-136981601660498332048854054076416)
def positiveArguments : Array ℕ := #[
    35334226544669, 425791477117051, 17667273808083, 69408329257, 143655326805, 1453211155215,
    11625688886685, 287306748225, 11625688886685, 537769654721069, 268826197096049, 2924636734165,
    6440390195975, 425791477117051, 5130983686869805, 212897672510581, 418204419179, 6645066477157,
    67221208892991, 537769654721069, 13289952302865, 287306748225, 13289952302865, 6643527216165,
    72276824025, 133615248841, 17667273808083, 212897672510581, 8833717172657, 277635837977,
    3321808761097, 33603275663211, 268826197096049, 6643527216165, 33595022647, 69408329257,
    418204419179, 277635837977, 34904502901, 36138903245, 365579602935, 2924636734165,
    72276824025, 38471237565, 1779564578381, 889588272401, 9678084085, 634790153775,
    29363497091935, 14678547194635, 159692093975, 38471237565, 634790153775, 7626124462305,
    39674806215, 39602379075, 7626124462305, 352761746759857, 176342413577797, 1918479322745,
    1779564578381, 29363497091935, 352761746759857
  ]
def positiveCoefficients : Array ℕ := #[
    9945700593749749802272292864, 119849646105117747377870995456, 9945790967341890332730064896, 312587325778233895495401472, 80870759533598103211868160, 3272340608558461012483768320,
    3272340508624992656016015360, 80869660265446182066585600, 3272340508624992656016015360, 151368701038310415214800011264, 151335695133649223786627596288, 3292848226544889591979048960,
    3625617360839200713421619200, 119849646105117747377870995456, 1444243513764434220475828142080, 119850734823337310153470902272, 3766850532758478221442285568, 3740839863797054971244969984,
    151368705660934269762187296768, 151368701038310415214800011264, 3740789014934654949984829440, 80869660265446182066585600, 3740789014934654949984829440, 3739973336893305328741908480,
    81376469436628228217241600, 300874792445671848770797568, 9945790967341890332730064896, 119850734823337310153470902272, 9945881341768604169134931968, 312590164114478150501531648,
    3740024174668124542392598528, 151335699755265116442414022656, 151335695133649223786627596288, 3739973336893305328741908480, 9456158217158285886226432, 312587325778233895495401472,
    3766850532758478221442285568, 312590164114478150501531648, 9824744141155999789613056, 81377575593880204355829760, 3292848327104639771628011520, 3292848226544889591979048960,
    81376469436628228217241600, 10828690697638489242992640, 500902898254900338869927936, 500793676512288361374810112, 10896553969716581934039040, 357355087499943731842252800,
    16530179320191638615852318720, 16526574919024606355642122240, 359594627459912114687180800, 10828690697638489242992640, 357355087499943731842252800, 4293126410839727771127644160,
    357358884971741277616865280, 11147078727822195503923200, 4293126410839727771127644160, 198587208907282157487609872384, 198543907019645115885659619328, 4320031381516191765637365760,
    500902898254900338869927936, 16530179320191638615852318720, 198587208907282157487609872384
  ]
def positiveScales : Array ℕ := #[
    45, 48, 44, 36, 37, 40,
    43, 38, 43, 48, 47, 41,
    42, 48, 52, 47, 38, 42,
    45, 48, 43, 38, 43, 42,
    36, 36, 44, 47, 43, 38,
    41, 44, 47, 42, 34, 36,
    38, 38, 35, 35, 38, 41,
    36, 35, 40, 39, 33, 39,
    44, 43, 37, 35, 39, 42,
    35, 35, 42, 48, 47, 40,
    40, 44, 48
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
    45006131562734070, 48597140400702327, 44006144672010749, 36014389750823015, 37063820533413007, 40402381484047545,
    43402381439989319, 38063800922870220, 43402381439989319, 48933981677010439, 47933667063444427, 41411394578946051,
    42550285236420590, 48597140400702327, 52188156862032232, 47597153506133117, 38605417350771624, 42595420770923755,
    45933981721068665, 48933981677010439, 43595401160380969, 38063800922870220, 43595401160380969, 42595086546812317,
    36072814061826953, 36959293707796243, 44006144672010749, 47597153506133117, 43006157781289367, 38014402850634477,
    41595106157355104, 44933667107502652, 47933667063444427, 42595086546812317, 34967528450824795, 36014389750823015,
    38605417350771624, 38014402850634477, 35022694114073353, 35072833672369740, 38411394623004277, 41411394578946051,
    36072814061826953, 35163061188702344, 40694661426209440, 39694346812640815, 33172074327659077, 39207488794476383,
    44739089031976471, 43738774418407893, 37216501933433116, 35163061188702344, 39207488794476383, 42794087215400081,
    35207504125347029, 35204868050304944, 42794087215400081, 48325687452946608, 47325372839377954, 40803100354349652,
    40694661426209440, 44739089031976471, 48325687452946608
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
noncomputable def positiveFloor : ℝ := 2130610111 / 1000000000000
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
    { argument := 9945700593749749802272292864, coefficient := (9945700593749749802272292864) }, { argument := 119849646105117747377870995456, coefficient := (119849646105117747377870995456) },
    { argument := 9945790967341890332730064896, coefficient := (9945790967341890332730064896) }, { argument := 312587325778233895495401472, coefficient := (312587325778233895495401472) },
    { argument := 80870759533598103211868160, coefficient := (80870759533598103211868160) }, { argument := 3272340608558461012483768320, coefficient := (3272340608558461012483768320) },
    { argument := 3272340508624992656016015360, coefficient := (3272340508624992656016015360) }, { argument := 80869660265446182066585600, coefficient := (80869660265446182066585600) },
    { argument := 3272340508624992656016015360, coefficient := (3272340508624992656016015360) }, { argument := 151368701038310415214800011264, coefficient := (151368701038310415214800011264) },
    { argument := 151335695133649223786627596288, coefficient := (151335695133649223786627596288) }, { argument := 3292848226544889591979048960, coefficient := (3292848226544889591979048960) },
    { argument := 3625617360839200713421619200, coefficient := (3625617360839200713421619200) }, { argument := 119849646105117747377870995456, coefficient := (119849646105117747377870995456) },
    { argument := 1444243513764434220475828142080, coefficient := (1444243513764434220475828142080) }, { argument := 119850734823337310153470902272, coefficient := (119850734823337310153470902272) },
    { argument := 3766850532758478221442285568, coefficient := (3766850532758478221442285568) }, { argument := 3740839863797054971244969984, coefficient := (3740839863797054971244969984) },
    { argument := 151368705660934269762187296768, coefficient := (151368705660934269762187296768) }, { argument := 151368701038310415214800011264, coefficient := (151368701038310415214800011264) },
    { argument := 3740789014934654949984829440, coefficient := (3740789014934654949984829440) }, { argument := 80869660265446182066585600, coefficient := (80869660265446182066585600) },
    { argument := 3740789014934654949984829440, coefficient := (3740789014934654949984829440) }, { argument := 3739973336893305328741908480, coefficient := (3739973336893305328741908480) },
    { argument := 81376469436628228217241600, coefficient := (81376469436628228217241600) }, { argument := 300874792445671848770797568, coefficient := (300874792445671848770797568) },
    { argument := 9945790967341890332730064896, coefficient := (9945790967341890332730064896) }, { argument := 119850734823337310153470902272, coefficient := (119850734823337310153470902272) },
    { argument := 9945881341768604169134931968, coefficient := (9945881341768604169134931968) }, { argument := 312590164114478150501531648, coefficient := (312590164114478150501531648) },
    { argument := 3740024174668124542392598528, coefficient := (3740024174668124542392598528) }, { argument := 151335699755265116442414022656, coefficient := (151335699755265116442414022656) },
    { argument := 151335695133649223786627596288, coefficient := (151335695133649223786627596288) }, { argument := 3739973336893305328741908480, coefficient := (3739973336893305328741908480) },
    { argument := 9456158217158285886226432, coefficient := (9456158217158285886226432) }, { argument := 312587325778233895495401472, coefficient := (312587325778233895495401472) },
    { argument := 3766850532758478221442285568, coefficient := (3766850532758478221442285568) }, { argument := 312590164114478150501531648, coefficient := (312590164114478150501531648) },
    { argument := 9824744141155999789613056, coefficient := (9824744141155999789613056) }, { argument := 81377575593880204355829760, coefficient := (81377575593880204355829760) },
    { argument := 3292848327104639771628011520, coefficient := (3292848327104639771628011520) }, { argument := 3292848226544889591979048960, coefficient := (3292848226544889591979048960) },
    { argument := 81376469436628228217241600, coefficient := (81376469436628228217241600) }, { argument := 3248354663084837841335301963776, coefficient := (-3248354663084837841335301963776) },
    { argument := 10828690697638489242992640, coefficient := (10828690697638489242992640) }, { argument := 500902898254900338869927936, coefficient := (500902898254900338869927936) },
    { argument := 500793676512288361374810112, coefficient := (500793676512288361374810112) }, { argument := 10896553969716581934039040, coefficient := (10896553969716581934039040) },
    { argument := 357355087499943731842252800, coefficient := (357355087499943731842252800) }, { argument := 16530179320191638615852318720, coefficient := (16530179320191638615852318720) },
    { argument := 16526574919024606355642122240, coefficient := (16526574919024606355642122240) }, { argument := 359594627459912114687180800, coefficient := (359594627459912114687180800) },
    { argument := 10828690697638489242992640, coefficient := (10828690697638489242992640) }, { argument := 357355087499943731842252800, coefficient := (357355087499943731842252800) },
    { argument := 4293126410839727771127644160, coefficient := (4293126410839727771127644160) }, { argument := 357358884971741277616865280, coefficient := (357358884971741277616865280) },
    { argument := 11147078727822195503923200, coefficient := (11147078727822195503923200) }, { argument := 4293126410839727771127644160, coefficient := (4293126410839727771127644160) },
    { argument := 198587208907282157487609872384, coefficient := (198587208907282157487609872384) }, { argument := 198543907019645115885659619328, coefficient := (198543907019645115885659619328) },
    { argument := 4320031381516191765637365760, coefficient := (4320031381516191765637365760) }, { argument := 500902898254900338869927936, coefficient := (500902898254900338869927936) },
    { argument := 16530179320191638615852318720, coefficient := (16530179320191638615852318720) }, { argument := 198587208907282157487609872384, coefficient := (198587208907282157487609872384) }] }

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
def constantNumerator : ℤ := (-78457769771865098885813621489664)
def positiveArguments : Array ℕ := #[
    1835238070391, 1831887807155, 39674806215, 1835238070391, 917418948611, 9980861935,
    889588272401, 14678547194635, 176342413577797, 917418948611, 915744182255, 39602379075,
    1831887807155, 915744182255, 9962641675, 9678084085, 159692093975, 1918479322745,
    9980861935, 9962641675
  ]
def positiveCoefficients : Array ℕ := #[
    16530354979898111416569167872, 515630577855488314761543680, 357358884971741277616865280, 16530354979898111416569167872, 16526750540428527275526324224, 359598448730418941347758080,
    500793676512288361374810112, 16526574919024606355642122240, 198543907019645115885659619328, 16526750540428527275526324224, 515518144746289696929218560, 11147078727822195503923200,
    515630577855488314761543680, 515518144746289696929218560, 11216937333788943528755200, 10896553969716581934039040, 359594627459912114687180800, 4320031381516191765637365760,
    359598448730418941347758080, 11216937333788943528755200
  ]
def positiveScales : Array ℕ := #[
    40, 40, 35, 40, 39, 33,
    39, 43, 47, 39, 39, 35,
    40, 39, 33, 33, 37, 40,
    33, 33
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
    40739104362847112, 40736468287805652, 35207504125347029, 40739104362847112, 39738789749278535, 33216517264303761,
    39694346812640815, 43738774418407893, 47325372839377954, 39738789749278535, 39736153674237070, 35204868050304944,
    40736468287805652, 39736153674237070, 33213881189261677, 33172074327659077, 37216501933433116, 40803100354349652,
    33216517264303761, 33213881189261677
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
noncomputable def positiveFloor : ℝ := 78902147 / 500000000000
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
    { argument := 16530354979898111416569167872, coefficient := (16530354979898111416569167872) }, { argument := 515630577855488314761543680, coefficient := (515630577855488314761543680) },
    { argument := 357358884971741277616865280, coefficient := (357358884971741277616865280) }, { argument := 16530354979898111416569167872, coefficient := (16530354979898111416569167872) },
    { argument := 16526750540428527275526324224, coefficient := (16526750540428527275526324224) }, { argument := 359598448730418941347758080, coefficient := (359598448730418941347758080) },
    { argument := 500793676512288361374810112, coefficient := (500793676512288361374810112) }, { argument := 16526574919024606355642122240, coefficient := (16526574919024606355642122240) },
    { argument := 198543907019645115885659619328, coefficient := (198543907019645115885659619328) }, { argument := 16526750540428527275526324224, coefficient := (16526750540428527275526324224) },
    { argument := 515518144746289696929218560, coefficient := (515518144746289696929218560) }, { argument := 11147078727822195503923200, coefficient := (11147078727822195503923200) },
    { argument := 515630577855488314761543680, coefficient := (515630577855488314761543680) }, { argument := 515518144746289696929218560, coefficient := (515518144746289696929218560) },
    { argument := 11216937333788943528755200, coefficient := (11216937333788943528755200) }, { argument := 10896553969716581934039040, coefficient := (10896553969716581934039040) },
    { argument := 359594627459912114687180800, coefficient := (359594627459912114687180800) }, { argument := 4320031381516191765637365760, coefficient := (4320031381516191765637365760) },
    { argument := 359598448730418941347758080, coefficient := (359598448730418941347758080) }, { argument := 11216937333788943528755200, coefficient := (11216937333788943528755200) },
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

end MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch1
