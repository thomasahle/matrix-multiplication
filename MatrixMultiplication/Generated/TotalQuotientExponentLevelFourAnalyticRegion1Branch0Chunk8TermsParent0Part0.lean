import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    129, 185, 243, 479, 487, 1755,
    1913, 2533, 2559, 3453, 6917, 8005,
    16023, 24329
  ]
def positiveCoefficients : Array ℕ := #[
    126685831860308675812076776587264, 950737950171172051122527404032, 429892009802398295782569474523136, 10141204801825835211973625643008, 430129694289941088795350106374144, 2224726803400542599626714125434880,
    9982748476797306536786537742336, 100778222718144237418987904827392, 101887416993343938145297520132096, 452155123468906574646355324567552, 452868176931534953684697220120576, 187057691696178101058357266743296,
    187295376183720894071137898594304, 716935642591577990883979206590464
  ]
def positiveScales : Array ℕ := #[
    7, 7, 7, 8, 8, 10,
    10, 11, 11, 11, 12, 12,
    13, 14
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 11, 23, 25, 35,
    51, 57, 71, 225, 361, 363,
    383, 775, 793, 1161, 1165, 1599,
    1875, 1879, 2713, 5429, 609920256803
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 792281625142643375935439503360, 1743019575313815427057966907392, 1822247737828079764651510857728, 3961408125713216879677197516800, 5545971375998503631548076523520,
    4040636288227481217270741467136, 36128042106504537942656041353216, 5625199538512767969141620473856, 35652673131418951917094777651200, 57202733335298851742538732142592, 57519645985355909092912907943936,
    60688772485926482596654665957376, 61401825948554861634996561510400, 125655865747623239423360705232896, 91983896679060895946104526340096, 92300809329117953296478702141440, 126685831860308675812076776587264,
    297105609428491265975789813760000, 297739434728605380676538165362688, 429892009802398295782569474523136, 430129694289941088795350106374144, 1112363401700271299813357062717440
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 4, 5,
    5, 5, 6, 7, 8, 8,
    8, 9, 9, 10, 10, 10,
    10, 10, 11, 12, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 7531381460516264, 7924812503187618, 8903881845446830, 8927777961642114, 10777255315166917,
    10901621158068202, 11306631361712500, 11321364432039446, 11753634618838289, 12755930741068530, 12966685686553403,
    13967856668746464, 14570389401646840
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 3459431618637364, 4523561956057598, 4643856189792934, 5129283016944967,
    5672425342008812, 5832890015409720, 6149747119504683, 7813781192070436, 8495855026887407, 8503825737996059,
    8581200581928289, 9598052500166958, 9631177055717079, 10181152256865567, 10186114239541643, 10642954223498123,
    10872674882924346, 10875749354229199, 11405673332281875, 12406470768529293, 39149829675559072
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 736544526053 / 1000000000000
noncomputable def negativeCeiling : ℝ := 50697590199 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 11, coefficient := (-1743019575313815427057966907392) }, { argument := 23, coefficient := (-1822247737828079764651510857728) }, { argument := 25, coefficient := (-3961408125713216879677197516800) }, { argument := 35, coefficient := (-5545971375998503631548076523520) }, { argument := 51, coefficient := (-4040636288227481217270741467136) }, { argument := 57, coefficient := (-36128042106504537942656041353216) }, { argument := 71, coefficient := (-5625199538512767969141620473856) }, { argument := 129, coefficient := 126685831860308675812076776587264 }, { argument := 185, coefficient := 950737950171172051122527404032 }, { argument := 225, coefficient := (-35652673131418951917094777651200) }, { argument := 243, coefficient := 429892009802398295782569474523136 }, { argument := 361, coefficient := (-57202733335298851742538732142592) }, { argument := 363, coefficient := (-57519645985355909092912907943936) }, { argument := 383, coefficient := (-60688772485926482596654665957376) }, { argument := 479, coefficient := 10141204801825835211973625643008 }, { argument := 487, coefficient := 430129694289941088795350106374144 }, { argument := 775, coefficient := (-61401825948554861634996561510400) }, { argument := 793, coefficient := (-125655865747623239423360705232896) }, { argument := 1161, coefficient := (-91983896679060895946104526340096) }, { argument := 1165, coefficient := (-92300809329117953296478702141440) }, { argument := 1599, coefficient := (-126685831860308675812076776587264) }, { argument := 1755, coefficient := 2224726803400542599626714125434880 }, { argument := 1875, coefficient := (-297105609428491265975789813760000) }, { argument := 1879, coefficient := (-297739434728605380676538165362688) }, { argument := 1913, coefficient := 9982748476797306536786537742336 }, { argument := 2533, coefficient := 100778222718144237418987904827392 }, { argument := 2559, coefficient := 101887416993343938145297520132096 }, { argument := 2713, coefficient := (-429892009802398295782569474523136) }, { argument := 3453, coefficient := 452155123468906574646355324567552 }, { argument := 5429, coefficient := (-430129694289941088795350106374144) }, { argument := 6917, coefficient := 452868176931534953684697220120576 }, { argument := 8005, coefficient := 187057691696178101058357266743296 }, { argument := 16023, coefficient := 187295376183720894071137898594304 }, { argument := 24329, coefficient := 716935642591577990883979206590464 }, { argument := 609920256803, coefficient := (-1112363401700271299813357062717440) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk8
