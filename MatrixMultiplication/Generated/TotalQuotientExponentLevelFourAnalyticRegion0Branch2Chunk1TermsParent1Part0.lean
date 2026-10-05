import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-46531512409005526696505276104704)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    512457215787, 24841479219051, 12422472977145, 63649500783, 45434505873, 1079645220399,
    14385065091561, 1078440365469, 22584421341, 45434505873, 1841775351765, 460581983175,
    22441412415, 1819677792483, 88209291770659, 44110800878305, 226012200647, 1841775351765,
    44415145725819, 594622940614413, 44347010363553, 913323961473, 1079645220399, 44415145725819,
    11106950697639, 533504924637, 512457215787, 1819677792483, 256229370873, 256229370873,
    12420776595129, 6211254983955, 31824845157, 460581983175, 11106950697639, 148697377568863,
    11089916711113, 228400056373, 14385065091561, 594622940614413, 148697377568863, 7109392914119,
    24841479219051, 88209291770659, 12420776595129, 22441412415, 533504924637, 7109392914119,
    532902772559, 11154301799, 1078440365469, 44347010363553, 11089916711113, 532902772559,
    12422472977145, 44110800878305, 6211254983955, 22584421341, 913323961473, 228400056373,
    11154301799, 63649500783, 226012200647, 31824845157
  ]
def negativeCoefficients : Array ℕ := #[
    144243882878853441254326272, 6992254784640625223669907456, 6993230583861284759131914240, 143325934004318446691549184, 12788676482462838253682688, 303893113267579589171871744,
    4049035861628403095244374016, 303553976754218120106737664, 12713898941963234697019392, 12788676482462838253682688, 518413674244313637023907840, 518569211950123514540851200,
    12633392073732702842388480, 512193764260050346702798848, 24828708346809701981753442304, 24832173299818568209305436160, 508934231307507487479955456, 518413674244313637023907840,
    12501752108775295406271627264, 167371478361063684914364284928, 12482573709268300946649120768, 514155681569793505625112576, 303893113267579589171871744, 12501752108775295406271627264,
    12505314755777367746581364736, 300336572474439718869663744, 144243882878853441254326272, 512193764260050346702798848, 144244312398127427670245376, 144244312398127427670245376,
    6992275605684392807783989248, 6993251407810718527830097920, 143326360790188934270287872, 518569211950123514540851200, 12505314755777367746581364736, 167418363552525339303463616512,
    12486136191934585834162880512, 514311204386421540078485504, 4049035861628403095244374016, 167371478361063684914364284928, 167418363552525339303463616512, 4002232409857096633840304128,
    6992254784640625223669907456, 24828708346809701981753442304, 6992275605684392807783989248, 12633392073732702842388480, 300336572474439718869663744, 4002232409857096633840304128,
    299997590990177072639377408, 12558627356388613293080576, 303553976754218120106737664, 12482573709268300946649120768, 12486136191934585834162880512, 299997590990177072639377408,
    6993230583861284759131914240, 24832173299818568209305436160, 6993251407810718527830097920, 12713898941963234697019392, 514155681569793505625112576, 514311204386421540078485504,
    12558627356388613293080576, 143325934004318446691549184, 508934231307507487479955456, 143326360790188934270287872
  ]
def negativeScales : Array ℕ := #[
    38, 44, 43, 35, 35, 39,
    43, 39, 34, 35, 40, 38,
    34, 40, 46, 45, 37, 40,
    45, 49, 45, 39, 39, 45,
    43, 38, 38, 40, 37, 37,
    43, 42, 34, 38, 43, 47,
    43, 37, 43, 49, 47, 42,
    44, 46, 43, 34, 38, 42,
    38, 33, 39, 45, 43, 38,
    43, 45, 42, 34, 39, 37,
    33, 35, 37, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38898640609424867, 44497816316854833, 43498017637103899, 35889430151280075, 35403069337655466, 39973694463857696,
    43709636982827295, 39972083555689102, 34394608898329174, 35403069337655466, 40744234240091411, 38744667021543251,
    34385444427850238, 40726820156053168, 46325995867610905, 45326197187859969, 37717609698536152, 40744234240091411,
    45336116958253625, 49078968452065891, 45333902082615444, 39732335727463134, 39973694463857696, 45336116958253625,
    43336528027110675, 38956710643662271, 38898640609424867, 40726820156053168, 37898644905374470, 37898644905374470,
    43497820612804107, 42498021933053173, 34889434447229631, 38744667021543251, 43336528027110675, 47079372532627406,
    43334313763966312, 37732772050696943, 43709636982827295, 49078968452065891, 47079372532627406, 42692863509076864,
    44497816316854833, 46325995867610905, 43497820612804107, 34385444427850238, 38956710643662271, 42692863509076864,
    38955081394212725, 33376881160111873, 39972083555689102, 45333902082615444, 43334313763966312, 38955081394212725,
    43498017637103899, 45326197187859969, 42498021933053173, 34394608898329174, 39732335727463134, 37732772050696943,
    33376881160111873, 35889430151280075, 37717609698536152, 34889434447229631
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
noncomputable def negativeCeiling : ℝ := 53791417 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 144243882878853441254326272, coefficient := (-144243882878853441254326272) }, { argument := 6992254784640625223669907456, coefficient := (-6992254784640625223669907456) }, { argument := 6993230583861284759131914240, coefficient := (-6993230583861284759131914240) }, { argument := 143325934004318446691549184, coefficient := (-143325934004318446691549184) }, { argument := 12788676482462838253682688, coefficient := (-12788676482462838253682688) }, { argument := 303893113267579589171871744, coefficient := (-303893113267579589171871744) }, { argument := 4049035861628403095244374016, coefficient := (-4049035861628403095244374016) }, { argument := 303553976754218120106737664, coefficient := (-303553976754218120106737664) }, { argument := 12713898941963234697019392, coefficient := (-12713898941963234697019392) }, { argument := 12788676482462838253682688, coefficient := (-12788676482462838253682688) }, { argument := 518413674244313637023907840, coefficient := (-518413674244313637023907840) }, { argument := 518569211950123514540851200, coefficient := (-518569211950123514540851200) }, { argument := 12633392073732702842388480, coefficient := (-12633392073732702842388480) }, { argument := 512193764260050346702798848, coefficient := (-512193764260050346702798848) }, { argument := 24828708346809701981753442304, coefficient := (-24828708346809701981753442304) }, { argument := 24832173299818568209305436160, coefficient := (-24832173299818568209305436160) }, { argument := 508934231307507487479955456, coefficient := (-508934231307507487479955456) }, { argument := 518413674244313637023907840, coefficient := (-518413674244313637023907840) }, { argument := 12501752108775295406271627264, coefficient := (-12501752108775295406271627264) }, { argument := 167371478361063684914364284928, coefficient := (-167371478361063684914364284928) }, { argument := 12482573709268300946649120768, coefficient := (-12482573709268300946649120768) }, { argument := 514155681569793505625112576, coefficient := (-514155681569793505625112576) }, { argument := 303893113267579589171871744, coefficient := (-303893113267579589171871744) }, { argument := 12501752108775295406271627264, coefficient := (-12501752108775295406271627264) }, { argument := 12505314755777367746581364736, coefficient := (-12505314755777367746581364736) }, { argument := 300336572474439718869663744, coefficient := (-300336572474439718869663744) }, { argument := 144243882878853441254326272, coefficient := (-144243882878853441254326272) }, { argument := 512193764260050346702798848, coefficient := (-512193764260050346702798848) }, { argument := 144244312398127427670245376, coefficient := (-144244312398127427670245376) }, { argument := 144244312398127427670245376, coefficient := (-144244312398127427670245376) }, { argument := 6992275605684392807783989248, coefficient := (-6992275605684392807783989248) }, { argument := 6993251407810718527830097920, coefficient := (-6993251407810718527830097920) }, { argument := 143326360790188934270287872, coefficient := (-143326360790188934270287872) }, { argument := 518569211950123514540851200, coefficient := (-518569211950123514540851200) }, { argument := 12505314755777367746581364736, coefficient := (-12505314755777367746581364736) }, { argument := 167418363552525339303463616512, coefficient := (-167418363552525339303463616512) }, { argument := 12486136191934585834162880512, coefficient := (-12486136191934585834162880512) }, { argument := 514311204386421540078485504, coefficient := (-514311204386421540078485504) }, { argument := 4049035861628403095244374016, coefficient := (-4049035861628403095244374016) }, { argument := 167371478361063684914364284928, coefficient := (-167371478361063684914364284928) }, { argument := 167418363552525339303463616512, coefficient := (-167418363552525339303463616512) }, { argument := 4002232409857096633840304128, coefficient := (-4002232409857096633840304128) }, { argument := 6992254784640625223669907456, coefficient := (-6992254784640625223669907456) }, { argument := 24828708346809701981753442304, coefficient := (-24828708346809701981753442304) }, { argument := 6992275605684392807783989248, coefficient := (-6992275605684392807783989248) }, { argument := 12633392073732702842388480, coefficient := (-12633392073732702842388480) }, { argument := 300336572474439718869663744, coefficient := (-300336572474439718869663744) }, { argument := 4002232409857096633840304128, coefficient := (-4002232409857096633840304128) }, { argument := 299997590990177072639377408, coefficient := (-299997590990177072639377408) }, { argument := 12558627356388613293080576, coefficient := (-12558627356388613293080576) }, { argument := 303553976754218120106737664, coefficient := (-303553976754218120106737664) }, { argument := 12482573709268300946649120768, coefficient := (-12482573709268300946649120768) }, { argument := 12486136191934585834162880512, coefficient := (-12486136191934585834162880512) }, { argument := 299997590990177072639377408, coefficient := (-299997590990177072639377408) }, { argument := 6993230583861284759131914240, coefficient := (-6993230583861284759131914240) }, { argument := 24832173299818568209305436160, coefficient := (-24832173299818568209305436160) }, { argument := 6993251407810718527830097920, coefficient := (-6993251407810718527830097920) }, { argument := 12713898941963234697019392, coefficient := (-12713898941963234697019392) }, { argument := 514155681569793505625112576, coefficient := (-514155681569793505625112576) }, { argument := 514311204386421540078485504, coefficient := (-514311204386421540078485504) }, { argument := 12558627356388613293080576, coefficient := (-12558627356388613293080576) }, { argument := 143325934004318446691549184, coefficient := (-143325934004318446691549184) }, { argument := 508934231307507487479955456, coefficient := (-508934231307507487479955456) }, { argument := 143326360790188934270287872, coefficient := (-143326360790188934270287872) }] }

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

end TermShard0


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 48432988309347870798750330912768
def positiveArguments : Array ℕ := #[
    3, 3022437, 10732333, 1511223, 991449, 40951581,
    10240771, 489983, 224973, 5423403, 72599429, 5415137,
    111569, 169551, 8219023, 4110085, 21059
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 28546110370770163741495394304, 101364019284391656050483265536, 28546195373366855395109240832, 9363971054149253754947371008, 386776747069842776819868106752,
    386885389833147675877654396928, 9255517185503669482969628672, 2124809909501265385321660416, 51222593100589364921789054976, 685682220370149047893825159168, 51144522937894563947116232704,
    2107478824509133787387396096, 1601363919074062431254740992, 77626477474269440026414678016, 77637310582981142992534896640, 1591173052204029736883585024
  ]
def positiveScales : Array ℕ := #[
    1, 21, 23, 20, 19, 25,
    23, 18, 17, 22, 26, 22,
    16, 17, 22, 21, 14
  ]
def negativeArguments : Array ℕ := #[
    1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 792281625142643375935439503360, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21527280837422244, 23355460388178609, 20527285133371518, 19919179036386355, 25287415814657312,
    23287821000252942, 18902372169829621, 17779392342059830, 22370766946850354, 26113454865571572, 22368566407013800,
    16767576697291226, 17371359767740210, 22970535478526328, 21970736798772385, 14362149310248596
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 578196257 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 28546110370770163741495394304, coefficient := 28546110370770163741495394304 }, { argument := 101364019284391656050483265536, coefficient := 101364019284391656050483265536 }, { argument := 28546195373366855395109240832, coefficient := 28546195373366855395109240832 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 9363971054149253754947371008, coefficient := 9363971054149253754947371008 }, { argument := 386776747069842776819868106752, coefficient := 386776747069842776819868106752 }, { argument := 386885389833147675877654396928, coefficient := 386885389833147675877654396928 }, { argument := 9255517185503669482969628672, coefficient := 9255517185503669482969628672 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 2124809909501265385321660416, coefficient := 2124809909501265385321660416 }, { argument := 51222593100589364921789054976, coefficient := 51222593100589364921789054976 }, { argument := 685682220370149047893825159168, coefficient := 685682220370149047893825159168 }, { argument := 51144522937894563947116232704, coefficient := 51144522937894563947116232704 }, { argument := 2107478824509133787387396096, coefficient := 2107478824509133787387396096 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1601363919074062431254740992, coefficient := 1601363919074062431254740992 }, { argument := 77626477474269440026414678016, coefficient := 77626477474269440026414678016 }, { argument := 77637310582981142992534896640, coefficient := 77637310582981142992534896640 }, { argument := 1591173052204029736883585024, coefficient := 1591173052204029736883585024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard1


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk1
