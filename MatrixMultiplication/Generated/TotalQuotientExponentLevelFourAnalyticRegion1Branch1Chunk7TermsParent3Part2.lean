import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1777674416039000481442419424886784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    153515645745, 16176920515, 8554245, 715754745, 28011033351, 28011033351,
    715754745, 18781194915969057, 13527, 351, 67505270890613457, 21789,
    9392885863964295, 21789, 22707, 13527, 675, 1192924575,
    46685055585, 46685055585, 1192924575, 16459888215, 28557, 741,
    61196896089, 45999, 1028533797, 45999, 47937, 28557,
    1425, 6576390353123, 6576393342749, 7263, 21789, 45999,
    118629, 99261, 2776887, 84735, 99261, 89577,
    45999, 45999, 89577, 2776887, 89577, 7263,
    118629, 8554245, 4044227355, 153515645745, 16176920515, 8554245,
    7569, 22707, 47937, 123627, 103443, 2893881,
    88305, 103443, 93351, 47937
  ]
def negativeCoefficients : Array ℕ := #[
    176991489273017105869040517120, 18650719540059169855520112640, 157797968258809563363409920, 52813378402232965283897671680, 2066849453864159410412127780864, 2066849453864159410412127780864,
    52813378402232965283897671680, 5286436401570681190020538171392, 255517805655110763222663168, 13260405083897963760058368, 19001044551781947224391828897792, 411582573180986798244888576,
    5287724659610399793046660055040, 411582573180986798244888576, 428923102906084135469580288, 255517805655110763222663168, 12750389503748042076979200, 2750696791782966941869670400,
    107648409055424969292298321920, 107648409055424969292298321920, 2750696791782966941869670400, 75907836345993234994283151360, 269713239302616916735033344, 13997094255225628413394944,
    282220870064794996752783507456, 434448271691041620369604608, 75892398897678931995087863808, 434448271691041620369604608, 452752164178644365217890304, 269713239302616916735033344,
    13458744476178488859033600, 14808714571883833702695829504, 14808721303923103491269066752, 548776764241315730993184768, 411582573180986798244888576, 434448271691041620369604608,
    560209613496343142055542784, 7499949111297981656906858496, 13113478095516440488524644352, 400149723925959387182530560, 7499949111297981656906858496, 423015422436014209307246592,
    434448271691041620369604608, 434448271691041620369604608, 423015422436014209307246592, 13113478095516440488524644352, 423015422436014209307246592, 548776764241315730993184768,
    560209613496343142055542784, 157797968258809563363409920, 18650706748395076242552913920, 176991489273017105869040517120, 18650719540059169855520112640, 157797968258809563363409920,
    571897470541445513959440384, 428923102906084135469580288, 452752164178644365217890304, 583812001177725628833595392, 7815932097399755357445685248, 13665966639813291760655794176,
    417008572269804020595425280, 7815932097399755357445685248, 440837633542364250343735296, 452752164178644365217890304
  ]
def negativeScales : Array ℕ := #[
    37, 33, 23, 29, 34, 34,
    29, 54, 13, 8, 55, 14,
    53, 14, 14, 13, 9, 30,
    35, 35, 30, 33, 14, 9,
    35, 15, 29, 15, 15, 14,
    10, 42, 42, 12, 14, 15,
    16, 16, 21, 16, 16, 16,
    15, 15, 16, 21, 16, 12,
    16, 23, 31, 37, 33, 23,
    12, 14, 15, 16, 16, 21,
    16, 16, 16, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37159594740975035, 33913217952736435, 23028209096999409, 29414890088508350, 34705276155604808, 34705276155604808,
    29414890088508350, 54060138372696506, 13723554295483443, 8455327220304618, 55905849676926519, 14411312365441260,
    53060489901954237, 14411312365441260, 14470849492418713, 13723554295483443, 9398743691938200, 30151855682674544,
    35442241749689136, 35442241749689136, 30151855682674544, 33938235495341548, 14801556808026795, 9533329732306630,
    35832739431291580, 15489314877442711, 29937942063207998, 15489314877442711, 15548852004421171, 14801556808026795,
    10476746203939589, 42580433073893943, 42580433729742728, 12826349865815290, 14411312365441260, 15489314877442711,
    16856097210059176, 16598939368622512, 21405037040014770, 16370670380943905, 16598939368622512, 16450840729627935,
    15489314877442711, 15489314877442711, 16450840729627935, 21405037040014770, 16450840729627935, 12826349865815290,
    16856097210059176, 23028209096999409, 31913216963258337, 37159594740975035, 33913217952736435, 23028209096999409,
    12885886995081222, 14470849492418713, 15548852004421171, 16915634340856806, 16658476495620780, 21464574166992205,
    16430207507921289, 16658476495620780, 16510377856605633, 15548852004421171
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
noncomputable def negativeCeiling : ℝ := 21856805609 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 52813378402232965283897671680, coefficient := (-52813378402232965283897671680) }, { argument := 2066849453864159410412127780864, coefficient := (-2066849453864159410412127780864) }, { argument := 2066849453864159410412127780864, coefficient := (-2066849453864159410412127780864) }, { argument := 52813378402232965283897671680, coefficient := (-52813378402232965283897671680) }, { argument := 5286436401570681190020538171392, coefficient := (-5286436401570681190020538171392) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 19001044551781947224391828897792, coefficient := (-19001044551781947224391828897792) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 5287724659610399793046660055040, coefficient := (-5287724659610399793046660055040) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }, { argument := 107648409055424969292298321920, coefficient := (-107648409055424969292298321920) }, { argument := 2750696791782966941869670400, coefficient := (-2750696791782966941869670400) }, { argument := 75907836345993234994283151360, coefficient := (-75907836345993234994283151360) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 282220870064794996752783507456, coefficient := (-282220870064794996752783507456) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 75892398897678931995087863808, coefficient := (-75892398897678931995087863808) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 14808714571883833702695829504, coefficient := (-14808714571883833702695829504) }, { argument := 14808721303923103491269066752, coefficient := (-14808721303923103491269066752) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 400149723925959387182530560, coefficient := (-400149723925959387182530560) }, { argument := 7499949111297981656906858496, coefficient := (-7499949111297981656906858496) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 13113478095516440488524644352, coefficient := (-13113478095516440488524644352) }, { argument := 423015422436014209307246592, coefficient := (-423015422436014209307246592) }, { argument := 548776764241315730993184768, coefficient := (-548776764241315730993184768) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 18650706748395076242552913920, coefficient := (-18650706748395076242552913920) }, { argument := 176991489273017105869040517120, coefficient := (-176991489273017105869040517120) }, { argument := 18650719540059169855520112640, coefficient := (-18650719540059169855520112640) }, { argument := 157797968258809563363409920, coefficient := (-157797968258809563363409920) }, { argument := 571897470541445513959440384, coefficient := (-571897470541445513959440384) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 583812001177725628833595392, coefficient := (-583812001177725628833595392) }, { argument := 7815932097399755357445685248, coefficient := (-7815932097399755357445685248) }, { argument := 13665966639813291760655794176, coefficient := (-13665966639813291760655794176) }, { argument := 417008572269804020595425280, coefficient := (-417008572269804020595425280) }, { argument := 7815932097399755357445685248, coefficient := (-7815932097399755357445685248) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2429619908994075286938820571824128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    47937, 93351, 2893881, 93351, 7569, 123627,
    354634557, 167662111203, 6364320056457, 670648904779, 354634557, 36503491995,
    1428562700901, 1428562700901, 36503491995, 2199663, 1039944177, 39475451763,
    4159779561, 2199663, 1192924575, 46685055585, 46685055585, 1192924575,
    1334584161, 73647, 1911, 4961879727, 118629, 83394543,
    118629, 123627, 73647, 3675, 4509, 13527,
    28557, 73647, 61623, 1723941, 52605, 61623,
    55611, 28557, 28557, 55611, 1723941, 55611,
    4509, 73647, 96540765, 45641994435, 1732533716265, 182568102955,
    96540765, 715754745, 28011033351, 28011033351, 715754745, 354634557,
    167662111203, 6364320056457, 670648904779, 354634557
  ]
def negativeCoefficients : Array ℕ := #[
    452752164178644365217890304, 440837633542364250343735296, 13665966639813291760655794176, 440837633542364250343735296, 571897470541445513959440384, 583812001177725628833595392,
    6541852912672362184008794112, 773205014054893017941265088512, 7337561455289937731885079724032, 773205544360738727438848098304, 6541852912672362184008794112, 84171321828558788421211914240,
    3294041317096004060344328650752, 3294041317096004060344328650752, 84171321828558788421211914240, 162306481637632693745221632, 19183584084063506992340140032, 182048388966531880322441674752,
    19183597241203717565677830144, 162306481637632693745221632, 88022297337054942139829452800, 3444749089773599017353546301440, 3444749089773599017353546301440, 88022297337054942139829452800,
    98474929851173536404502216704, 347788124363900761053069312, 18048884697527784006746112, 366122101793987271398761955328, 560209613496343142055542784, 98454898679357847792078815232,
    560209613496343142055542784, 583812001177725628833595392, 347788124363900761053069312, 17354696824545946160332800, 340690407540147684296884224, 255517805655110763222663168,
    269713239302616916735033344, 347788124363900761053069312, 4656102236382018352057417728, 8141081196844779039344295936, 248420088831357686466478080, 4656102236382018352057417728,
    262615522478863839978848256, 269713239302616916735033344, 269713239302616916735033344, 262615522478863839978848256, 8141081196844779039344295936, 262615522478863839978848256,
    340690407540147684296884224, 347788124363900761053069312, 1780862784635136500815626240, 210486547589030146165954314240, 1997475378938335909093457264640, 210486691952096345512298414080,
    1780862784635136500815626240, 52813378402232965283897671680, 2066849453864159410412127780864, 2066849453864159410412127780864, 52813378402232965283897671680, 6541852912672362184008794112,
    773205014054893017941265088512, 7337561455289937731885079724032, 773205544360738727438848098304, 6541852912672362184008794112
  ]
def negativeScales : Array ℕ := #[
    15, 16, 21, 16, 12, 16,
    28, 37, 42, 39, 28, 35,
    40, 40, 35, 21, 29, 35,
    31, 21, 30, 35, 35, 30,
    30, 16, 10, 32, 16, 26,
    16, 16, 16, 11, 12, 13,
    14, 16, 15, 20, 15, 15,
    15, 14, 14, 15, 20, 15,
    12, 16, 26, 35, 40, 37,
    26, 29, 34, 34, 29, 28,
    37, 42, 39, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15548852004421171, 16510377856605633, 21464574166992205, 16510377856605633, 12885886995081222, 16915634340856806,
    28401757884121194, 37286765744855180, 42533143528097605, 39286766734333180, 28401757884121194, 35087315430479834,
    40377701497494393, 40377701497494393, 35087315430479834, 21068851081496754, 29953858953355033, 35200236725472381,
    31953859942833219, 21068851081496754, 30151855682674544, 35442241749689136, 35442241749689136, 30151855682674544,
    30313743140978939, 16168339138031573, 10900112067353854, 32208239619574604, 16856097210059176, 26313449646869317,
    16856097210059176, 16915634340856806, 16168339138031573, 11843528536141147, 12138591794637521, 13723554295483443,
    14801556808026795, 16168339138031573, 15911181303864252, 20717278970040312, 15682912310909503, 15911181303864252,
    15763082659843835, 14801556808026795, 14801556808026795, 15763082659843835, 20717278970040312, 15763082659843835,
    12138591794637521, 16168339138031573, 26524634923119512, 35409642783852910, 40656020567119349, 37409643773330911,
    26524634923119512, 29414890088508350, 34705276155604808, 34705276155604808, 29414890088508350, 28401757884121194,
    37286765744855180, 42533143528097605, 39286766734333180, 28401757884121194
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
noncomputable def negativeCeiling : ℝ := 1153919103 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 13665966639813291760655794176, coefficient := (-13665966639813291760655794176) }, { argument := 440837633542364250343735296, coefficient := (-440837633542364250343735296) }, { argument := 571897470541445513959440384, coefficient := (-571897470541445513959440384) }, { argument := 583812001177725628833595392, coefficient := (-583812001177725628833595392) }, { argument := 6541852912672362184008794112, coefficient := (-6541852912672362184008794112) }, { argument := 773205014054893017941265088512, coefficient := (-773205014054893017941265088512) }, { argument := 7337561455289937731885079724032, coefficient := (-7337561455289937731885079724032) }, { argument := 773205544360738727438848098304, coefficient := (-773205544360738727438848098304) }, { argument := 6541852912672362184008794112, coefficient := (-6541852912672362184008794112) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 3294041317096004060344328650752, coefficient := (-3294041317096004060344328650752) }, { argument := 84171321828558788421211914240, coefficient := (-84171321828558788421211914240) }, { argument := 162306481637632693745221632, coefficient := (-162306481637632693745221632) }, { argument := 19183584084063506992340140032, coefficient := (-19183584084063506992340140032) }, { argument := 182048388966531880322441674752, coefficient := (-182048388966531880322441674752) }, { argument := 19183597241203717565677830144, coefficient := (-19183597241203717565677830144) }, { argument := 162306481637632693745221632, coefficient := (-162306481637632693745221632) }, { argument := 88022297337054942139829452800, coefficient := (-88022297337054942139829452800) }, { argument := 3444749089773599017353546301440, coefficient := (-3444749089773599017353546301440) }, { argument := 3444749089773599017353546301440, coefficient := (-3444749089773599017353546301440) }, { argument := 88022297337054942139829452800, coefficient := (-88022297337054942139829452800) }, { argument := 98474929851173536404502216704, coefficient := (-98474929851173536404502216704) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 18048884697527784006746112, coefficient := (-18048884697527784006746112) }, { argument := 366122101793987271398761955328, coefficient := (-366122101793987271398761955328) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 98454898679357847792078815232, coefficient := (-98454898679357847792078815232) }, { argument := 560209613496343142055542784, coefficient := (-560209613496343142055542784) }, { argument := 583812001177725628833595392, coefficient := (-583812001177725628833595392) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 17354696824545946160332800, coefficient := (-17354696824545946160332800) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 248420088831357686466478080, coefficient := (-248420088831357686466478080) }, { argument := 4656102236382018352057417728, coefficient := (-4656102236382018352057417728) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 8141081196844779039344295936, coefficient := (-8141081196844779039344295936) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 340690407540147684296884224, coefficient := (-340690407540147684296884224) }, { argument := 347788124363900761053069312, coefficient := (-347788124363900761053069312) }, { argument := 1780862784635136500815626240, coefficient := (-1780862784635136500815626240) }, { argument := 210486547589030146165954314240, coefficient := (-210486547589030146165954314240) }, { argument := 1997475378938335909093457264640, coefficient := (-1997475378938335909093457264640) }, { argument := 210486691952096345512298414080, coefficient := (-210486691952096345512298414080) }, { argument := 1780862784635136500815626240, coefficient := (-1780862784635136500815626240) }, { argument := 52813378402232965283897671680, coefficient := (-52813378402232965283897671680) }, { argument := 2066849453864159410412127780864, coefficient := (-2066849453864159410412127780864) }, { argument := 2066849453864159410412127780864, coefficient := (-2066849453864159410412127780864) }, { argument := 52813378402232965283897671680, coefficient := (-52813378402232965283897671680) }, { argument := 6541852912672362184008794112, coefficient := (-6541852912672362184008794112) }, { argument := 773205014054893017941265088512, coefficient := (-773205014054893017941265088512) }, { argument := 7337561455289937731885079724032, coefficient := (-7337561455289937731885079724032) }, { argument := 773205544360738727438848098304, coefficient := (-773205544360738727438848098304) }, { argument := 6541852912672362184008794112, coefficient := (-6541852912672362184008794112) }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
