import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1623525617219019105705572836573184)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    855, 279, 15495583, 572231265, 4577848999, 123965785,
    324779503683, 855, 279, 590955745213, 2817, 324779503683,
    5643, 2529, 855, 279, 9424911123017, 9424910667191,
    10344798171, 1995, 651, 18835677221, 6573, 10344798171,
    13167, 5901, 1995, 651, 59076899625, 59076644055,
    5023777, 9405, 39501, 171171, 5643, 5643,
    13167, 171171, 171171, 5643, 2112363, 84645,
    39501, 171171, 13167, 84645, 13167, 171171,
    171171, 5643, 15495583, 572231265, 4577848999, 123965785,
    4215, 17703, 76713, 2529, 2529, 5901,
    76713, 76713, 2529, 946689
  ]
def negativeCoefficients : Array ℕ := #[
    129203946971313493046722560, 5270160994882524058484736, 2286744430991395799668097024, 84446429571440559710451793920, 84446408892640453082044432384, 2286765109791502428075458560,
    748890548103338717817618825216, 2067263151541015888747560960, 84322575918120384935755776, 2725302347708129869137342103552, 1702772016927205192573648896, 748890548103338717817618825216,
    1705492100021338108216737792, 1528686698902698591415959552, 2067263151541015888747560960, 84322575918120384935755776, 10866182712734567471639630446592, 10866182187202969712719000764416,
    23853480544326957342803361792, 150737938133199075221176320, 6148521160696278068232192, 86864229287696936585903734784, 124160459567608711958495232, 23853480544326957342803361792,
    124358798959889237057470464, 111466738461655105624080384, 150737938133199075221176320, 6148521160696278068232192, 136222056006325347777773568000, 136221466702027483034010255360,
    23724116122211417622726049792, 88827713542778026469621760, 1492305587518670844689645568, 3233328772957120163494232064, 106593256251333631763546112, 1705492100021338108216737792,
    124358798959889237057470464, 3233328772957120163494232064, 3233328772957120163494232064, 1705492100021338108216737792, 39901408923415889490154094592, 3197797687540008952906383360,
    1492305587518670844689645568, 3233328772957120163494232064, 124358798959889237057470464, 3197797687540008952906383360, 124358798959889237057470464, 3233328772957120163494232064,
    3233328772957120163494232064, 106593256251333631763546112, 2286744430991395799668097024, 84446429571440559710451793920, 84446408892640453082044432384, 2286765109791502428075458560,
    79619098901182218302914560, 1337600861539861267488964608, 2898135200003032746226089984, 95542918681418661963497472, 1528686698902698591415959552, 111466738461655105624080384,
    2898135200003032746226089984, 2898135200003032746226089984, 1528686698902698591415959552, 35764899226411052461669220352
  ]
def negativeScales : Array ℕ := #[
    9, 8, 23, 29, 32, 26,
    38, 9, 8, 39, 11, 38,
    12, 11, 9, 8, 43, 43,
    33, 10, 9, 34, 12, 33,
    13, 12, 10, 9, 35, 35,
    22, 13, 15, 17, 12, 12,
    13, 17, 17, 12, 21, 16,
    15, 17, 13, 16, 13, 17,
    17, 12, 23, 29, 32, 26,
    12, 14, 16, 11, 11, 12,
    16, 16, 11, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9739780609952834, 8124121311829188, 23885353702924620, 29092023083443334, 32092022730163673, 26885366749012717,
    38240669632971488, 9739780609952834, 8124121311829188, 39104259139388332, 11459943848374998, 38240669632971488,
    12462246634244425, 11304351321663239, 9739780609952834, 8124121311829188, 43099616152468676, 43099616082694232,
    33268186447088670, 10962173043893966, 9346513733165637, 34132748853983408, 12682336269758884, 33268186447088670,
    13684639055631019, 12526743743000334, 10962173043893966, 9346513733165637, 35781875064300134, 35781868823106454,
    22260340995310396, 13199212228410558, 15269601556301956, 17385078773721895, 12462246634244425, 12462246634244425,
    13684639055631019, 17385078773721895, 17385078773721895, 12462246634244425, 21010426345923797, 16369137229852872,
    15269601556301956, 17385078773721895, 13684639055631019, 16369137229852872, 13684639055631019, 17385078773721895,
    17385078773721895, 12462246634244425, 23885353702924620, 29092023083443334, 32092022730163673, 26885366749012717,
    12041316915829445, 14111706243720843, 16227183461140779, 11304351321663239, 11304351321663239, 12526743743000334,
    16227183461140779, 16227183461140779, 11304351321663239, 19852531035160402
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
noncomputable def negativeCeiling : ℝ := 1697665847 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 2286744430991395799668097024, coefficient := (-2286744430991395799668097024) }, { argument := 84446429571440559710451793920, coefficient := (-84446429571440559710451793920) }, { argument := 84446408892640453082044432384, coefficient := (-84446408892640453082044432384) }, { argument := 2286765109791502428075458560, coefficient := (-2286765109791502428075458560) }, { argument := 748890548103338717817618825216, coefficient := (-748890548103338717817618825216) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 2725302347708129869137342103552, coefficient := (-2725302347708129869137342103552) }, { argument := 1702772016927205192573648896, coefficient := (-1702772016927205192573648896) }, { argument := 748890548103338717817618825216, coefficient := (-748890548103338717817618825216) }, { argument := 1705492100021338108216737792, coefficient := (-1705492100021338108216737792) }, { argument := 1528686698902698591415959552, coefficient := (-1528686698902698591415959552) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 10866182712734567471639630446592, coefficient := (-10866182712734567471639630446592) }, { argument := 10866182187202969712719000764416, coefficient := (-10866182187202969712719000764416) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 86864229287696936585903734784, coefficient := (-86864229287696936585903734784) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 23853480544326957342803361792, coefficient := (-23853480544326957342803361792) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 136222056006325347777773568000, coefficient := (-136222056006325347777773568000) }, { argument := 136221466702027483034010255360, coefficient := (-136221466702027483034010255360) }, { argument := 23724116122211417622726049792, coefficient := (-23724116122211417622726049792) }, { argument := 88827713542778026469621760, coefficient := (-88827713542778026469621760) }, { argument := 1492305587518670844689645568, coefficient := (-1492305587518670844689645568) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 106593256251333631763546112, coefficient := (-106593256251333631763546112) }, { argument := 1705492100021338108216737792, coefficient := (-1705492100021338108216737792) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 1705492100021338108216737792, coefficient := (-1705492100021338108216737792) }, { argument := 39901408923415889490154094592, coefficient := (-39901408923415889490154094592) }, { argument := 3197797687540008952906383360, coefficient := (-3197797687540008952906383360) }, { argument := 1492305587518670844689645568, coefficient := (-1492305587518670844689645568) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3197797687540008952906383360, coefficient := (-3197797687540008952906383360) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 106593256251333631763546112, coefficient := (-106593256251333631763546112) }, { argument := 2286744430991395799668097024, coefficient := (-2286744430991395799668097024) }, { argument := 84446429571440559710451793920, coefficient := (-84446429571440559710451793920) }, { argument := 84446408892640453082044432384, coefficient := (-84446408892640453082044432384) }, { argument := 2286765109791502428075458560, coefficient := (-2286765109791502428075458560) }, { argument := 79619098901182218302914560, coefficient := (-79619098901182218302914560) }, { argument := 1337600861539861267488964608, coefficient := (-1337600861539861267488964608) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 95542918681418661963497472, coefficient := (-95542918681418661963497472) }, { argument := 1528686698902698591415959552, coefficient := (-1528686698902698591415959552) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 1528686698902698591415959552, coefficient := (-1528686698902698591415959552) }, { argument := 35764899226411052461669220352, coefficient := (-35764899226411052461669220352) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1011337960044824957349546191486976)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37935, 17703, 76713, 5901, 37935, 5901,
    76713, 76713, 2529, 524403151, 19365510705, 154924047703,
    4195263145, 316538558151, 25935, 8463, 576245700921, 85449,
    316538558151, 171171, 76713, 25935, 8463, 28544495,
    1054110225, 8432879735, 228358025, 180022420041, 25935, 8463,
    327976390071, 85449, 180022420041, 171171, 76713, 25935,
    8463, 104941778295, 104941193865, 1425, 5985, 25935,
    855, 855, 1995, 25935, 25935, 855,
    320055, 12825, 5985, 25935, 1995, 12825,
    1995, 25935, 25935, 855, 948492791, 35026576905,
    280212546623, 7588010945, 324779503683, 855
  ]
def negativeCoefficients : Array ℕ := #[
    2866287560442559858904924160, 1337600861539861267488964608, 2898135200003032746226089984, 111466738461655105624080384, 2866287560442559858904924160, 111466738461655105624080384,
    2898135200003032746226089984, 2898135200003032746226089984, 95542918681418661963497472, 38694122871775460504910168064, 1428922479327270523521592197120, 1428922129420205561361962369024,
    38694472778840422664539996160, 729888221459065691810669002752, 3919186391463175955750584320, 159861550178103229774036992, 2657464242116265864883637059584, 3228171948757826510920876032,
    729888221459065691810669002752, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320, 159861550178103229774036992, 2106211975913127710220615680,
    77779606184221568154363494400, 77779587137958312049251450880, 2106231022176383815332659200, 415103438753271045756165292032, 3919186391463175955750584320, 159861550178103229774036992,
    1512524132464717869191931101184, 3228171948757826510920876032, 415103438753271045756165292032, 3233328772957120163494232064, 2898135200003032746226089984, 3919186391463175955750584320,
    159861550178103229774036992, 120989632927989556494383185920, 120988959126074619114805002240, 107669955809427910872268800, 1808855257598388902654115840, 3919186391463175955750584320,
    129203946971313493046722560, 2067263151541015888747560960, 150737938133199075221176320, 3919186391463175955750584320, 3919186391463175955750584320, 2067263151541015888747560960,
    48365344149595017563823144960, 3876118409139404791401676800, 1808855257598388902654115840, 3919186391463175955750584320, 150737938133199075221176320, 3876118409139404791401676800,
    150737938133199075221176320, 3919186391463175955750584320, 3919186391463175955750584320, 129203946971313493046722560, 69986415085341929342473601024, 2584505199778562393243564113920,
    2584504566898443340379412496384, 69987047965460982206625218560, 748890548103338717817618825216, 2067263151541015888747560960
  ]
def negativeScales : Array ℕ := #[
    15, 14, 16, 12, 15, 12,
    16, 16, 11, 28, 34, 37,
    31, 38, 14, 13, 39, 16,
    38, 17, 16, 14, 13, 24,
    29, 32, 27, 37, 14, 13,
    38, 16, 37, 17, 16, 14,
    13, 36, 36, 10, 12, 14,
    9, 9, 10, 14, 14, 9,
    18, 13, 12, 14, 10, 13,
    10, 14, 14, 9, 29, 35,
    38, 32, 38, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15211241917271758, 14111706243720843, 16227183461140779, 12526743743000334, 15211241917271758, 12526743743000334,
    16227183461140779, 16227183461140779, 11304351321663239, 28966101127104179, 34172770497327696, 37172770144048035,
    31966114173194429, 38203590291487405, 14662612749280074, 13046953451306728, 39067893126121895, 16382775987852475,
    38203590291487405, 17385078773721895, 16227183461140779, 14662612749280074, 13046953451306728, 24766709203397615,
    29973378602332297, 32973378249052547, 27766722249485004, 37389385635136710, 14662612749280074, 13046953451306728,
    38254801007526733, 16382775987852475, 37389385635136710, 17385078773721895, 16227183461140779, 14662612749280074,
    13046953451306728, 36610798186314211, 36610790151796172, 10476746203939589, 12547135531832084, 14662612749280074,
    9739780609952834, 9739780609952834, 10962173043893966, 14662612749280074, 14662612749280074, 9739780609952834,
    18287960321452706, 13646671205401350, 12547135531832084, 14662612749280074, 10962173043893966, 13646671205401350,
    10962173043893966, 14662612749280074, 14662612749280074, 9739780609952834, 29821061568589827, 35027730951472967,
    38027730598193306, 32821074614677381, 38240669632971488, 9739780609952834
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
noncomputable def negativeCeiling : ℝ := 888859473 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2866287560442559858904924160, coefficient := (-2866287560442559858904924160) }, { argument := 1337600861539861267488964608, coefficient := (-1337600861539861267488964608) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2866287560442559858904924160, coefficient := (-2866287560442559858904924160) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 95542918681418661963497472, coefficient := (-95542918681418661963497472) }, { argument := 38694122871775460504910168064, coefficient := (-38694122871775460504910168064) }, { argument := 1428922479327270523521592197120, coefficient := (-1428922479327270523521592197120) }, { argument := 1428922129420205561361962369024, coefficient := (-1428922129420205561361962369024) }, { argument := 38694472778840422664539996160, coefficient := (-38694472778840422664539996160) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 2657464242116265864883637059584, coefficient := (-2657464242116265864883637059584) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 729888221459065691810669002752, coefficient := (-729888221459065691810669002752) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 2106211975913127710220615680, coefficient := (-2106211975913127710220615680) }, { argument := 77779606184221568154363494400, coefficient := (-77779606184221568154363494400) }, { argument := 77779587137958312049251450880, coefficient := (-77779587137958312049251450880) }, { argument := 2106231022176383815332659200, coefficient := (-2106231022176383815332659200) }, { argument := 415103438753271045756165292032, coefficient := (-415103438753271045756165292032) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 1512524132464717869191931101184, coefficient := (-1512524132464717869191931101184) }, { argument := 3228171948757826510920876032, coefficient := (-3228171948757826510920876032) }, { argument := 415103438753271045756165292032, coefficient := (-415103438753271045756165292032) }, { argument := 3233328772957120163494232064, coefficient := (-3233328772957120163494232064) }, { argument := 2898135200003032746226089984, coefficient := (-2898135200003032746226089984) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 120989632927989556494383185920, coefficient := (-120989632927989556494383185920) }, { argument := 120988959126074619114805002240, coefficient := (-120988959126074619114805002240) }, { argument := 107669955809427910872268800, coefficient := (-107669955809427910872268800) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 48365344149595017563823144960, coefficient := (-48365344149595017563823144960) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 69986415085341929342473601024, coefficient := (-69986415085341929342473601024) }, { argument := 2584505199778562393243564113920, coefficient := (-2584505199778562393243564113920) }, { argument := 2584504566898443340379412496384, coefficient := (-2584504566898443340379412496384) }, { argument := 69987047965460982206625218560, coefficient := (-69987047965460982206625218560) }, { argument := 748890548103338717817618825216, coefficient := (-748890548103338717817618825216) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
