import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 308978449763831512253150875548123136
def positiveArguments : Array ℕ := #[
    40839, 135, 567, 2457, 81, 81,
    189, 2457, 2457, 81, 30321, 1215,
    567, 2457, 189, 1215, 189, 2457,
    2457, 81, 27, 513, 783, 8073,
    243, 783, 243, 243, 20817, 243,
    8073, 20817, 27, 243, 243, 513,
    105
  ]
def positiveCoefficients : Array ℕ := #[
    3235598928920041282982741387771904, 10445119081470396069461360640, 175478000568702653966950858752, 380202334565522416928393527296, 12534142897764475283353632768, 200546286364231604533658124288,
    14623166714058554497245904896, 380202334565522416928393527296, 380202334565522416928393527296, 200546286364231604533658124288, 4691947491396501914402043199488, 376024286932934258500608983040,
    175478000568702653966950858752, 380202334565522416928393527296, 14623166714058554497245904896, 376024286932934258500608983040, 14623166714058554497245904896, 380202334565522416928393527296,
    380202334565522416928393527296, 12534142897764475283353632768, 66848762121410534844552708096, 79382905019175010127906340864, 60581690672528297202875891712, 624618121071929684953789366272,
    75204857386586851700121796608, 60581690672528297202875891712, 75204857386586851700121796608, 75204857386586851700121796608, 3221274724725470147821883621376, 75204857386586851700121796608,
    624618121071929684953789366272, 3221274724725470147821883621376, 66848762121410534844552708096, 75204857386586851700121796608, 75204857386586851700121796608, 79382905019175010127906340864,
    8123981507810308054025502720
  ]
def positiveScales : Array ℕ := #[
    15, 7, 9, 11, 6, 6,
    7, 11, 11, 6, 14, 10,
    9, 11, 7, 10, 7, 11,
    11, 6, 4, 9, 9, 12,
    7, 9, 7, 7, 14, 7,
    12, 14, 4, 7, 7, 9,
    6
  ]
def negativeArguments : Array ℕ := #[
    8073, 5245, 20817, 20817, 121489, 2409,
    2124786860150051, 2124786234438365, 368026087, 9799, 40634475, 1111456185,
    325075695, 243, 243, 47, 243, 243,
    2409, 47, 513, 513, 1225, 9733,
    10955055, 27, 27
  ]
def negativeCoefficients : Array ℕ := #[
    156154530267982421238447341568, 101453054782059680341342289920, 805318681181367536955470905344, 805318681181367536955470905344, 2349939022386586940894057857024, 186387347164905067639499390976,
    4784594655806747940084565147648, 4784593246829289984602165739520, 6951816232281872236299270750208, 189540225702460020527133097984, 749573760894548932401561600, 2562843474229572129647493120,
    749573518781032964963696640, 18801214346646712925030449152, 18801214346646712925030449152, 7272897730801609115032354816, 18801214346646712925030449152, 18801214346646712925030449152,
    186387347164905067639499390976, 7272897730801609115032354816, 19845726254793752531976585216, 19845726254793752531976585216, 189559568515573854593928396800, 188263600036946972118643376128,
    51733784549993521146526433280, 8556641551540548460102746636288, 8556641551540548460102746636288
  ]
def negativeScales : Array ℕ := #[
    12, 12, 14, 14, 16, 11,
    50, 50, 28, 13, 25, 30,
    28, 7, 7, 5, 7, 7,
    11, 5, 9, 9, 10, 13,
    23, 4, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15317659919792980, 7076815597050830, 9147204924942228, 11262682142362164, 6339850002884624, 6339850002884624,
    7562242424220952, 11262682142362164, 11262682142362164, 6339850002884624, 14888029714346523, 10246740598493143,
    9147204924942228, 11262682142362164, 7562242424220952, 10246740598493143, 7562242424220952, 11262682142362164,
    11262682142362164, 6339850002884624, 4754887502147955, 9002815015607054, 9612868497290540, 12978889175322745,
    7924812503187618, 9612868497290540, 7924812503187618, 7924812503187618, 14345474552078502, 7924812503187618,
    12978889175322745, 14345474552078502, 4754887502147955, 7924812503187618, 7924812503187618, 9002815015607054,
    6714245517659862
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12978889193202904, 12356727057464632, 14345474552078504, 14345474552078504, 16890466171666790, 11234218678238471,
    50916239559222271, 50916239134374307, 28455232792369363, 13258418812598833, 25276200918881397, 30049803930620043,
    28276200452888531, 7924812510375204, 7924812510375204, 5554588851679165, 7924812510375204, 7924812510375204,
    11234218678238471, 5554588851679165, 9002815015607055, 9002815015607055, 10258566033889934, 13248668839723137,
    23385093391627587, 4754887502413606, 4754887502413606
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
noncomputable def positiveFloor : ℝ := 599287643933 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2545815673 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 101453054782059680341342289920, coefficient := (-101453054782059680341342289920) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 2349939022386586940894057857024, coefficient := (-2349939022386586940894057857024) }, { argument := 186387347164905067639499390976, coefficient := (-186387347164905067639499390976) }, { argument := 4784594655806747940084565147648, coefficient := (-4784594655806747940084565147648) }, { argument := 4784593246829289984602165739520, coefficient := (-4784593246829289984602165739520) }, { argument := 6951816232281872236299270750208, coefficient := (-6951816232281872236299270750208) }, { argument := 189540225702460020527133097984, coefficient := (-189540225702460020527133097984) }, { argument := 749573760894548932401561600, coefficient := (-749573760894548932401561600) }, { argument := 2562843474229572129647493120, coefficient := (-2562843474229572129647493120) }, { argument := 749573518781032964963696640, coefficient := (-749573518781032964963696640) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 7272897730801609115032354816, coefficient := (-7272897730801609115032354816) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 186387347164905067639499390976, coefficient := (-186387347164905067639499390976) }, { argument := 7272897730801609115032354816, coefficient := (-7272897730801609115032354816) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 189559568515573854593928396800, coefficient := (-189559568515573854593928396800) }, { argument := 188263600036946972118643376128, coefficient := (-188263600036946972118643376128) }, { argument := 51733784549993521146526433280, coefficient := (-51733784549993521146526433280) }, { argument := 3235598928920041282982741387771904, coefficient := 3235598928920041282982741387771904 }, { argument := 10445119081470396069461360640, coefficient := 10445119081470396069461360640 }, { argument := 175478000568702653966950858752, coefficient := 175478000568702653966950858752 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 200546286364231604533658124288, coefficient := 200546286364231604533658124288 }, { argument := 14623166714058554497245904896, coefficient := 14623166714058554497245904896 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 200546286364231604533658124288, coefficient := 200546286364231604533658124288 }, { argument := 4691947491396501914402043199488, coefficient := 4691947491396501914402043199488 }, { argument := 376024286932934258500608983040, coefficient := 376024286932934258500608983040 }, { argument := 175478000568702653966950858752, coefficient := 175478000568702653966950858752 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 14623166714058554497245904896, coefficient := 14623166714058554497245904896 }, { argument := 376024286932934258500608983040, coefficient := 376024286932934258500608983040 }, { argument := 14623166714058554497245904896, coefficient := 14623166714058554497245904896 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 380202334565522416928393527296, coefficient := 380202334565522416928393527296 }, { argument := 12534142897764475283353632768, coefficient := 12534142897764475283353632768 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 60581690672528297202875891712, coefficient := 60581690672528297202875891712 }, { argument := 624618121071929684953789366272, coefficient := 624618121071929684953789366272 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 60581690672528297202875891712, coefficient := 60581690672528297202875891712 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 3221274724725470147821883621376, coefficient := 3221274724725470147821883621376 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 624618121071929684953789366272, coefficient := 624618121071929684953789366272 }, { argument := 3221274724725470147821883621376, coefficient := 3221274724725470147821883621376 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-161278242985571714867929225820635136)
def positiveArguments : Array ℕ := #[
    1869, 105, 3325, 5677, 105, 5677,
    5677, 1869, 105, 1123, 4838654671, 4838653233,
    122154089737, 431075429453, 61077044053, 126004921, 9368674953, 74945847607,
    2019630833, 19429003, 2926863007, 153, 29946310923, 157,
    5, 153, 87, 157, 2451, 3,
    1463431535, 153, 5, 3, 5, 77,
    87, 19428077
  ]
def positiveCoefficients : Array ℕ := #[
    144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864, 8123981507810308054025502720, 219618300094471994393822756864,
    219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 177946453007037702235099712454656, 731196820496353609515614194368512, 731196603191937533786020040933376,
    576856379119459714707173725437952, 2035696159637485478311749157388288, 576856371417279981146782381899776, 19041325299425199950393363136512, 707877065391160778840800764100608, 707843517539106012463634730450944,
    19074873907058603586702630977536, 91750872562773785465835225088, 13821719764207863779181432143872, 5918900812833224439361437696, 141417454988368348848039194001408, 6073643317743896973723828224,
    193428131138340667952988160, 5918900812833224439361437696, 3365649481807127622381993984, 6073643317743896973723828224, 94818469884014595430554796032, 3713820117856140824697372672,
    13821720061716952199969080606720, 5918900812833224439361437696, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160, 5957586439060892572952035328,
    3365649481807127622381993984, 91746499651410648174367342592
  ]
def positiveScales : Array ℕ := #[
    10, 6, 11, 12, 6, 12,
    12, 10, 6, 10, 32, 32,
    36, 38, 35, 26, 33, 36,
    30, 24, 31, 7, 34, 7,
    2, 7, 6, 7, 11, 1,
    30, 7, 2, 1, 2, 6,
    6, 24
  ]
def negativeArguments : Array ℕ := #[
    7, 1123, 9229, 629, 9175, 1069
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 177946453007037702235099712454656, 1462393423688291143301634235301888, 3189408910174225174165705264726016, 1453836782136750594841531488665600, 169389811455497153774996965818368
  ]
def negativeScales : Array ℕ := #[
    2, 10, 13, 9, 13, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10868050853594526, 6714245517659862, 11699138625271509, 12470913026274870, 6714245517659862, 12470913026274870,
    12470913026274870, 10868050853594526, 6714245517659862, 10133142212400601, 32171958833454438, 32171958404699770,
    36829911209745473, 38649149377520536, 35829911190482626, 26908904836663787, 33125197870503102, 36125129496389757,
    30911444461447509, 24211708535085382, 31446708075391632, 7257387842692651, 34801659237625888, 7294620748891626,
    2321928094887362, 7257387842692651, 6442943495848725, 7294620748891626, 11259154768866839, 1584962500720924,
    30446708106445284, 7257387842692651, 2321928094887362, 1584962500720924, 2321928094887362, 6266786540694901,
    6442943495848725, 24211639773582556
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 10133142212400602, 13171958619077121, 9296916206879290, 13163492442617938, 10062046137720491
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 1356341154399 / 500000000000
noncomputable def negativeCeiling : ℝ := 861402275427 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 177946453007037702235099712454656, coefficient := 177946453007037702235099712454656 }, { argument := 177946453007037702235099712454656, coefficient := (-177946453007037702235099712454656) }, { argument := 731196820496353609515614194368512, coefficient := 731196820496353609515614194368512 }, { argument := 731196603191937533786020040933376, coefficient := 731196603191937533786020040933376 }, { argument := 1462393423688291143301634235301888, coefficient := (-1462393423688291143301634235301888) }, { argument := 576856379119459714707173725437952, coefficient := 576856379119459714707173725437952 }, { argument := 2035696159637485478311749157388288, coefficient := 2035696159637485478311749157388288 }, { argument := 576856371417279981146782381899776, coefficient := 576856371417279981146782381899776 }, { argument := 3189408910174225174165705264726016, coefficient := (-3189408910174225174165705264726016) }, { argument := 19041325299425199950393363136512, coefficient := 19041325299425199950393363136512 }, { argument := 707877065391160778840800764100608, coefficient := 707877065391160778840800764100608 }, { argument := 707843517539106012463634730450944, coefficient := 707843517539106012463634730450944 }, { argument := 19074873907058603586702630977536, coefficient := 19074873907058603586702630977536 }, { argument := 1453836782136750594841531488665600, coefficient := (-1453836782136750594841531488665600) }, { argument := 91750872562773785465835225088, coefficient := 91750872562773785465835225088 }, { argument := 13821719764207863779181432143872, coefficient := 13821719764207863779181432143872 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 141417454988368348848039194001408, coefficient := 141417454988368348848039194001408 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 13821720061716952199969080606720, coefficient := 13821720061716952199969080606720 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 91746499651410648174367342592, coefficient := 91746499651410648174367342592 }, { argument := 169389811455497153774996965818368, coefficient := (-169389811455497153774996965818368) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
