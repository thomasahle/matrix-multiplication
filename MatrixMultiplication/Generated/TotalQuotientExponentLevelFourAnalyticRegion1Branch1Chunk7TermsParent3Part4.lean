import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2125322953150977253850573048905728)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1192924575, 2199663, 1039944177, 39475451763, 4159779561, 2199663,
    37457831655, 1465910745369, 1465910745369, 37457831655, 8452337169, 28557,
    741, 31424582847, 45999, 528163539, 45999, 47937,
    28557, 1425, 1192924575, 46685055585, 46685055585, 1192924575,
    16459888215, 28557, 741, 61196896089, 45999, 1028533797,
    45999, 47937, 28557, 1425, 7021264059, 7021265733,
    8554245, 4044227355, 153515645745, 16176920515, 8554245, 36503491995,
    1428562700901, 1428562700901, 36503491995, 16459814487, 55611, 1443,
    61195240281, 89577, 1028528997, 89577, 93351, 55611,
    2775, 1192924575, 46685055585, 46685055585, 1192924575, 517370827065,
    1723941, 44733, 1923488762391, 2776887
  ]
def negativeCoefficients : Array ℕ := #[
    2750696791782966941869670400, 162306481637632693745221632, 19183584084063506992340140032, 182048388966531880322441674752, 19183597241203717565677830144, 162306481637632693745221632,
    86371879261985161974707650560, 3380160044340344035778167308288, 3380160044340344035778167308288, 86371879261985161974707650560, 77959050290622859417120407552, 269713239302616916735033344,
    13997094255225628413394944, 289840618700846039686107365376, 434448271691041620369604608, 77943181063981709116877832192, 434448271691041620369604608, 452752164178644365217890304,
    269713239302616916735033344, 13458744476178488859033600, 2750696791782966941869670400, 107648409055424969292298321920, 107648409055424969292298321920, 2750696791782966941869670400,
    75907836345993234994283151360, 269713239302616916735033344, 13997094255225628413394944, 282220870064794996752783507456, 434448271691041620369604608, 75892398897678931995087863808,
    434448271691041620369604608, 452752164178644365217890304, 269713239302616916735033344, 13458744476178488859033600, 8094966323144257597901635584, 8094968253134856309763473408,
    157797968258809563363409920, 18650706748395076242552913920, 176991489273017105869040517120, 18650719540059169855520112640, 157797968258809563363409920, 84171321828558788421211914240,
    3294041317096004060344328650752, 3294041317096004060344328650752, 84171321828558788421211914240, 75907496335606468379827765248, 262615522478863839978848256, 13628749669561796086726656,
    282213233998192196536472961024, 423015422436014209307246592, 75892044720192716771696836608, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256,
    13104566989963265468006400, 88022297337054942139829452800, 3444749089773599017353546301440, 3444749089773599017353546301440, 88022297337054942139829452800, 2385951809517874510540056821760,
    8141081196844779039344295936, 422491239756415678688526336, 8870526232120774779563843518464, 13113478095516440488524644352
  ]
def negativeScales : Array ℕ := #[
    30, 21, 29, 35, 31, 21,
    35, 40, 40, 35, 32, 14,
    9, 34, 15, 28, 15, 15,
    14, 10, 30, 35, 35, 30,
    33, 14, 9, 35, 15, 29,
    15, 15, 14, 10, 32, 32,
    23, 31, 37, 33, 23, 35,
    40, 40, 35, 33, 15, 10,
    35, 16, 29, 16, 16, 15,
    11, 30, 35, 35, 30, 38,
    20, 15, 40, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30151855682674544, 21068851081496754, 29953858953355033, 35200236725472381, 31953859942833219, 21068851081496754,
    35124548336678809, 40414934403693378, 40414934403693378, 35124548336678809, 32976703188661749, 14801556808026795,
    9533329732306630, 34871174544833465, 15489314877442711, 28976409485864359, 15489314877442711, 15548852004421171,
    14801556808026795, 10476746203939589, 30151855682674544, 35442241749689136, 35442241749689136, 30151855682674544,
    33938235495341548, 14801556808026795, 9533329732306630, 35832739431291580, 15489314877442711, 29937942063207998,
    15489314877442711, 15548852004421171, 14801556808026795, 10476746203939589, 32709083640657185, 32709083984622487,
    23028209096999409, 31913216963258337, 37159594740975035, 33913217952736435, 23028209096999409, 35087315430479834,
    40377701497494393, 40377701497494393, 35087315430479834, 33938229033130362, 15763082659843835, 10494855584491427,
    35832700395678359, 16450840729627935, 29937935330368122, 16450840729627935, 16510377856605633, 15763082659843835,
    11438272056124861, 30151855682674544, 35442241749689136, 35442241749689136, 30151855682674544, 38912407756428473,
    20717278970040312, 15449051894878119, 40806862540384876, 21405037040014770
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
noncomputable def negativeCeiling : ℝ := 15945945391 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 162306481637632693745221632, coefficient := (-162306481637632693745221632) }, { argument := 19183584084063506992340140032, coefficient := (-19183584084063506992340140032) }, { argument := 182048388966531880322441674752, coefficient := (-182048388966531880322441674752) }, { argument := 19183597241203717565677830144, coefficient := (-19183597241203717565677830144) }, { argument := 162306481637632693745221632, coefficient := (-162306481637632693745221632) }, { argument := 86371879261985161974707650560, coefficient := (-86371879261985161974707650560) }, { argument := 3380160044340344035778167308288, coefficient := (-3380160044340344035778167308288) }, { argument := 3380160044340344035778167308288, coefficient := (-3380160044340344035778167308288) }, { argument := 86371879261985161974707650560, coefficient := (-86371879261985161974707650560) }, { argument := 77959050290622859417120407552, coefficient := (-77959050290622859417120407552) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 289840618700846039686107365376, coefficient := (-289840618700846039686107365376) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 77943181063981709116877832192, coefficient := (-77943181063981709116877832192) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }, { argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 75907836345993234994283151360, coefficient := (-75907836345993234994283151360) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 282220870064794996752783507456, coefficient := (-282220870064794996752783507456) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 75892398897678931995087863808, coefficient := (-75892398897678931995087863808) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 8094966323144257597901635584, coefficient := (-8094966323144257597901635584) }, { argument := 8094968253134856309763473408, coefficient := (-8094968253134856309763473408) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }, { argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 75907496335606468379827765248, coefficient := (-75907496335606468379827765248) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 282213233998192196536472961024, coefficient := (-282213233998192196536472961024) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 75892044720192716771696836608, coefficient := (-75892044720192716771696836608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 88022297337054942139829452800, coefficient := (-88022297337054942139829452800) }, { argument := 3444749089773599017353546301440, coefficient := (-3444749089773599017353546301440) }, { argument := 3444749089773599017353546301440, coefficient := (-3444749089773599017353546301440) }, { argument := 88022297337054942139829452800, coefficient := (-88022297337054942139829452800) }, { argument := 2385951809517874510540056821760, coefficient := (-2385951809517874510540056821760) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 422491239756415678688526336, coefficient := (-422491239756415678688526336) }, { argument := 8870526232120774779563843518464, coefficient := (-8870526232120774779563843518464) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }] }

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

end TermShard8


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-361402467468989177832545686913024)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    32329091403, 2776887, 2893881, 1723941, 86025, 70892117757,
    70892134659, 16459814487, 55611, 1443, 61195240281, 89577,
    1028528997, 89577, 93351, 55611, 2775, 144275651793,
    144275686191, 1025, 100437847917, 8662185, 494759473448989, 97758945,
    8662185, 123689883786235, 8662185, 8662185, 359109441, 2227419,
    97758945, 359109441, 12856120430967, 8662185, 2227419, 8662185,
    437690037790675, 4509, 117, 1615462572422681, 7263, 109410923833477,
    7263, 7569, 4509, 225, 824037942101, 824038317227,
    1334584161, 73647, 1911, 4961879727, 118629, 83394543,
    118629, 123627, 73647, 3675, 21516776955, 21516782085,
    509, 7021264059, 7021265733, 1025
  ]
def negativeCoefficients : Array ℕ := #[
    2385465900986818653871241428992, 13113478095516440488524644352, 13665966639813291760655794176, 8141081196844779039344295936, 406241576688861229508198400, 163466094138332427622142705664,
    163466133111690969351997882368, 75907496335606468379827765248, 262615522478863839978848256, 13628749669561796086726656, 282213233998192196536472961024, 423015422436014209307246592,
    75892044720192716771696836608, 423015422436014209307246592, 440837633542364250343735296, 262615522478863839978848256, 13104566989963265468006400, 166338501543319099673011027968,
    166338541201513015139333308416, 19826383441679918465181286400, 7237309671246331965773709312, 159789109814125772364840960, 278524822532861208725257453568, 1803334239330848002403205120,
    159789109814125772364840960, 278524857264593950458804961280, 159789109814125772364840960, 159789109814125772364840960, 6624399952579899877182406656, 164354512951672223003836416,
    1803334239330848002403205120, 6624399952579899877182406656, 7237352397791650205562568704, 159789109814125772364840960, 164354512951672223003836416, 159789109814125772364840960,
    123198793193616390144969932800, 340690407540147684296884224, 17680540111863951680077824, 454712289949610566198268788736, 548776764241315730993184768, 123185748951677184237421723648,
    548776764241315730993184768, 571897470541445513959440384, 340690407540147684296884224, 17000519338330722769305600, 14844547875940855830894608384, 14844554633610111098833338368,
    98474929851173536404502216704, 347788124363900761053069312, 18048884697527784006746112, 366122101793987271398761955328, 560209613496343142055542784, 98454898679357847792078815232,
    560209613496343142055542784, 583812001177725628833595392, 347788124363900761053069312, 17354696824545946160332800, 198457238889988250787265904640, 198457286205886799852265799680,
    19690983749883079997614194688, 8094966323144257597901635584, 8094968253134856309763473408, 19826383441679918465181286400
  ]
def negativeScales : Array ℕ := #[
    34, 21, 21, 20, 16, 36,
    36, 33, 15, 10, 35, 16,
    29, 16, 16, 15, 11, 37,
    37, 10, 36, 23, 48, 26,
    23, 46, 23, 23, 28, 21,
    26, 28, 43, 23, 21, 23,
    48, 12, 6, 50, 12, 46,
    12, 12, 12, 7, 39, 39,
    30, 16, 10, 32, 16, 26,
    16, 16, 16, 11, 34, 34,
    8, 32, 32, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34912113915922234, 21405037040014770, 21464574166992205, 20717278970040312, 16392468366511711, 36044906177113426,
    36044906521078728, 33938229033130362, 15763082659843835, 10494855584491427, 35832700395678359, 16450840729627935,
    29937935330368122, 16450840729627935, 16510377856605633, 15763082659843835, 11438272056124861, 37070036892437108,
    37070037236402410, 10001408194392809, 36547512065171100, 23046299553982304, 48813720660938378, 26542725380102868,
    23046299553982304, 46813720840840822, 23046299553982304, 23046299553982304, 28419848341104097, 21086941538479650,
    26542725380102868, 28419848341104097, 43547520582312952, 23046299553982304, 21086941538479650, 23046299553982304,
    48636902875783872, 12138591794637521, 6870364722125690, 50520868749460092, 12826349865815290, 46636750115687650,
    12826349865815290, 12885886995081222, 12138591794637521, 7813781192070436, 39583919810324455, 39583920467080982,
    30313743140978939, 16168339138031573, 10900112067353854, 32208239619574604, 16856097210059176, 26313449646869317,
    16856097210059176, 16915634340856806, 16168339138031573, 11843528536141147, 34324742938511756, 34324743282477058,
    8991521866745102, 32709083640657185, 32709083984622487, 10001408194392809
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
noncomputable def negativeCeiling : ℝ := 2634959023 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2385465900986818653871241428992, coefficient := (-2385465900986818653871241428992) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 13665966639813291760655794176, coefficient := (-13665966639813291760655794176) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 406241576688861229508198400, coefficient := (-406241576688861229508198400) }, { argument := 163466094138332427622142705664, coefficient := (-163466094138332427622142705664) }, { argument := 163466133111690969351997882368, coefficient := (-163466133111690969351997882368) }, { argument := 75907496335606468379827765248, coefficient := (-75907496335606468379827765248) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 282213233998192196536472961024, coefficient := (-282213233998192196536472961024) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 75892044720192716771696836608, coefficient := (-75892044720192716771696836608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 13104566989963265468006400, coefficient := (-13104566989963265468006400) }, { argument := 166338501543319099673011027968, coefficient := (-166338501543319099673011027968) }, { argument := 166338541201513015139333308416, coefficient := (-166338541201513015139333308416) }, { argument := 19826383441679918465181286400, coefficient := (-19826383441679918465181286400) }, { argument := 7237309671246331965773709312, coefficient := (-7237309671246331965773709312) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 278524822532861208725257453568, coefficient := (-278524822532861208725257453568) }, { argument := 1803334239330848002403205120, coefficient := (-1803334239330848002403205120) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 278524857264593950458804961280, coefficient := (-278524857264593950458804961280) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 6624399952579899877182406656, coefficient := (-6624399952579899877182406656) }, { argument := 164354512951672223003836416, coefficient := (-164354512951672223003836416) }, { argument := 1803334239330848002403205120, coefficient := (-1803334239330848002403205120) }, { argument := 6624399952579899877182406656, coefficient := (-6624399952579899877182406656) }, { argument := 7237352397791650205562568704, coefficient := (-7237352397791650205562568704) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 164354512951672223003836416, coefficient := (-164354512951672223003836416) }, { argument := 159789109814125772364840960, coefficient := (-159789109814125772364840960) }, { argument := 123198793193616390144969932800, coefficient := (-123198793193616390144969932800) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 17680540111863951680077824, coefficient := (-17680540111863951680077824) }, { argument := 454712289949610566198268788736, coefficient := (-454712289949610566198268788736) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 123185748951677184237421723648, coefficient := (-123185748951677184237421723648) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 571897470541445513959440384, coefficient := (-571897470541445513959440384) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 17000519338330722769305600, coefficient := (-17000519338330722769305600) }, { argument := 14844547875940855830894608384, coefficient := (-14844547875940855830894608384) }, { argument := 14844554633610111098833338368, coefficient := (-14844554633610111098833338368) }, { argument := 98474929851173536404502216704, coefficient := (-98474929851173536404502216704) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 18048884697527784006746112, coefficient := (-18048884697527784006746112) }, { argument := 366122101793987271398761955328, coefficient := (-366122101793987271398761955328) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 98454898679357847792078815232, coefficient := (-98454898679357847792078815232) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 583812001177725628833595392, coefficient := (-583812001177725628833595392) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 17354696824545946160332800, coefficient := (-17354696824545946160332800) }, { argument := 198457238889988250787265904640, coefficient := (-198457238889988250787265904640) }, { argument := 198457286205886799852265799680, coefficient := (-198457286205886799852265799680) }, { argument := 19690983749883079997614194688, coefficient := (-19690983749883079997614194688) }, { argument := 8094966323144257597901635584, coefficient := (-8094966323144257597901635584) }, { argument := 8094968253134856309763473408, coefficient := (-8094968253134856309763473408) }, { argument := 19826383441679918465181286400, coefficient := (-19826383441679918465181286400) }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
