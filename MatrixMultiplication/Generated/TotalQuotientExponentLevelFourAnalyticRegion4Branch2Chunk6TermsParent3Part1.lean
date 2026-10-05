import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6

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
def constantNumerator : ℤ := 162793688148110139188145584865280
def positiveArguments : Array ℕ := #[
    5, 1, 135, 17, 17, 29,
    17, 135, 135, 29, 2451, 29,
    135, 135, 17, 29
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 618970019642690137449562112, 5222559540735198034730680320, 5261245166962866168321277952, 657655645870358271040159744, 4487532642409503496509325312,
    657655645870358271040159744, 5222559540735198034730680320, 5222559540735198034730680320, 4487532642409503496509325312, 94818469884014595430554796032, 4487532642409503496509325312,
    5222559540735198034730680320, 5222559540735198034730680320, 657655645870358271040159744, 4487532642409503496509325312
  ]
def positiveScales : Array ℕ := #[
    2, 0, 7, 4, 4, 4,
    4, 7, 7, 4, 11, 4,
    7, 7, 4, 4
  ]
def negativeArguments : Array ℕ := #[
    35880189, 424531, 2114894722755, 1976265, 248863, 424531,
    248863, 1976265, 1976265, 74715870689, 2114978829789, 81857121664047,
    81857080915761, 2114894722755, 24916743638029, 43924932860051, 24910966457037, 31620375,
    1100841165, 275210595, 1976265, 3981825, 138624443, 34656149,
    248863, 6792525, 236476991, 59119313, 424531, 3981825,
    138624443, 34656149, 248863, 31620375, 1100841165, 275210595,
    1976265, 31620375, 1100841165, 275210595, 1976265, 18679642721,
    2865431615461, 1432715355227, 74715870689, 275834762935, 486260308265, 275770808055
  ]
def negativeCoefficients : Array ℕ := #[
    661872663799328643087335424, 31324858833423958628368384, 595289942832952902974177280, 36455654676829607024394240, 4590712070415580143812608, 31324858833423958628368384,
    4590712070415580143812608, 36455654676829607024394240, 36455654676829607024394240, 21030647962102660264361984, 595313616858389255326531584, 23040731413988964041156984832,
    23040719944366111192007049216, 595289942832952902974177280, 7013439835219598829131137024, 24727538907599967340736806912, 7011813703334422384604086272, 36455810321232728948736000,
    1269183452284954292036567040, 1269184853084582389355642880, 36455654676829607024394240, 4590731670081158460211200, 159823101398846096034234368, 159823277795836300881821696,
    4590712070415580143812608, 31324992572318493022617600, 1090557633074479243527716864, 1090558836724530053075959808, 31324858833423958628368384, 4590731670081158460211200,
    159823101398846096034234368, 159823277795836300881821696, 4590712070415580143812608, 36455810321232728948736000, 1269183452284954292036567040, 1269184853084582389355642880,
    36455654676829607024394240, 36455810321232728948736000, 1269183452284954292036567040, 1269184853084582389355642880, 36455654676829607024394240, 21031407999427399494139904,
    806547297227862374053052416, 806547042491038126072397824, 21030647962102660264361984, 155281166946236887696670720, 547480435776829129081487360, 155245163549519822098268160
  ]
def negativeScales : Array ℕ := #[
    25, 18, 40, 20, 17, 18,
    17, 20, 20, 36, 40, 46,
    46, 40, 44, 45, 44, 24,
    30, 28, 20, 21, 27, 25,
    17, 22, 27, 25, 18, 21,
    27, 25, 17, 24, 30, 28,
    20, 24, 30, 28, 20, 34,
    41, 40, 36, 38, 38, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 0, 7076815597050830, 4087462841250339, 4087462841250339, 4857980995002857,
    4087462841250339, 7076815597050830, 7076815597050830, 4857980995002857, 11259154768866839, 4857980995002857,
    7076815597050830, 7076815597050830, 4087462841250339, 4857980995002857
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25096684153929262, 18695510380255104, 40943722997304385, 20914344987749163, 17924992233103382, 18695510380255104,
    17924992233103382, 20914344987749163, 20914344987749163, 36120695672910485, 40943780370565651, 46218173171828893,
    46218172453658456, 40943722997304385, 44502180768822494, 45320105314589044, 44501846227644944, 24914351147203807,
    30035959178476622, 28035960770780365, 20914344987749163, 21924998392558141, 27046606422676130, 25046608014979873,
    17924992233103382, 22695516539709145, 27817124577465684, 25817126169769456, 18695510380255104, 21924998392558141,
    27046606422676130, 25046608014979873, 17924992233103382, 24914351147203807, 30035959178476622, 28035960770780365,
    20914344987749163, 24914351147203807, 30035959178476622, 28035960770780365, 20914344987749163, 34120747810261089,
    41381889604885482, 40381889149230107, 36120695672910485, 38005013332206417, 38822937878997163, 38004678791028871
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 30383857 / 500000000000
noncomputable def negativeCeiling : ℝ := 52627613 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 661872663799328643087335424, coefficient := (-661872663799328643087335424) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 595289942832952902974177280, coefficient := (-595289942832952902974177280) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 21030647962102660264361984, coefficient := (-21030647962102660264361984) }, { argument := 595313616858389255326531584, coefficient := (-595313616858389255326531584) }, { argument := 23040731413988964041156984832, coefficient := (-23040731413988964041156984832) }, { argument := 23040719944366111192007049216, coefficient := (-23040719944366111192007049216) }, { argument := 595289942832952902974177280, coefficient := (-595289942832952902974177280) }, { argument := 7013439835219598829131137024, coefficient := (-7013439835219598829131137024) }, { argument := 24727538907599967340736806912, coefficient := (-24727538907599967340736806912) }, { argument := 7011813703334422384604086272, coefficient := (-7011813703334422384604086272) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 31324992572318493022617600, coefficient := (-31324992572318493022617600) }, { argument := 1090557633074479243527716864, coefficient := (-1090557633074479243527716864) }, { argument := 1090558836724530053075959808, coefficient := (-1090558836724530053075959808) }, { argument := 31324858833423958628368384, coefficient := (-31324858833423958628368384) }, { argument := 4590731670081158460211200, coefficient := (-4590731670081158460211200) }, { argument := 159823101398846096034234368, coefficient := (-159823101398846096034234368) }, { argument := 159823277795836300881821696, coefficient := (-159823277795836300881821696) }, { argument := 4590712070415580143812608, coefficient := (-4590712070415580143812608) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 36455810321232728948736000, coefficient := (-36455810321232728948736000) }, { argument := 1269183452284954292036567040, coefficient := (-1269183452284954292036567040) }, { argument := 1269184853084582389355642880, coefficient := (-1269184853084582389355642880) }, { argument := 36455654676829607024394240, coefficient := (-36455654676829607024394240) }, { argument := 21031407999427399494139904, coefficient := (-21031407999427399494139904) }, { argument := 806547297227862374053052416, coefficient := (-806547297227862374053052416) }, { argument := 806547042491038126072397824, coefficient := (-806547042491038126072397824) }, { argument := 21030647962102660264361984, coefficient := (-21030647962102660264361984) }, { argument := 155281166946236887696670720, coefficient := (-155281166946236887696670720) }, { argument := 547480435776829129081487360, coefficient := (-547480435776829129081487360) }, { argument := 155245163549519822098268160, coefficient := (-155245163549519822098268160) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 4487532642409503496509325312, coefficient := 4487532642409503496509325312 }] }

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
def constantNumerator : ℤ := (-85591467575149778411493219368960)
def positiveArguments : Array ℕ := #[
    17, 135, 135, 1, 3036323, 5352637,
    3035619, 119531, 73585027, 73584997, 239053, 68853,
    1182143, 7171433, 9457287, 284957, 90845, 8207613,
    8206223, 90845
  ]
def positiveCoefficients : Array ℕ := #[
    657655645870358271040159744, 5222559540735198034730680320, 5222559540735198034730680320, 618970019642690137449562112, 28677259932732419528370159616, 101108454255071716590808465408,
    28670610840724539067909275648, 18063014018044529985225490432, 694990930291715761060481859584, 694990646949726788881769037824, 18062333997270996756314718208, 2601192795560189455188885504,
    89320199698543536029667688448, 1083716314667049868281329483776, 89321550295357636748198805504, 2691342771718170982318342144, 1716013532545171677752852480, 77518713071130354722638135296,
    77505584892307977108944060416, 1716013532545171677752852480
  ]
def positiveScales : Array ℕ := #[
    4, 7, 7, 0, 21, 22,
    21, 16, 26, 26, 17, 16,
    20, 22, 23, 18, 16, 22,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 9, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 158456325028528675187087900672, 1426106925256758076683791106048, 1267650600228229401496703205376, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0, 3, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 7076815597050830, 7076815597050830, 0, 21533893840219664, 22351818385986556,
    21533559299042118, 16867025299577136, 26132908902363116, 26132908314188296, 17866970985216224, 16071231895069189,
    20172973133530226, 22773829997213735, 23172994948132087, 18120384707513737, 16471119491986694, 22968531275983318,
    22968286927729481, 16471119491986694
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 3169925001442313, 0, 0
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 876093059 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5441537 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 5222559540735198034730680320, coefficient := 5222559540735198034730680320 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28677259932732419528370159616, coefficient := 28677259932732419528370159616 }, { argument := 101108454255071716590808465408, coefficient := 101108454255071716590808465408 }, { argument := 28670610840724539067909275648, coefficient := 28670610840724539067909275648 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 18063014018044529985225490432, coefficient := 18063014018044529985225490432 }, { argument := 694990930291715761060481859584, coefficient := 694990930291715761060481859584 }, { argument := 694990646949726788881769037824, coefficient := 694990646949726788881769037824 }, { argument := 18062333997270996756314718208, coefficient := 18062333997270996756314718208 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2601192795560189455188885504, coefficient := 2601192795560189455188885504 }, { argument := 89320199698543536029667688448, coefficient := 89320199698543536029667688448 }, { argument := 1083716314667049868281329483776, coefficient := 1083716314667049868281329483776 }, { argument := 89321550295357636748198805504, coefficient := 89321550295357636748198805504 }, { argument := 2691342771718170982318342144, coefficient := 2691342771718170982318342144 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 77518713071130354722638135296, coefficient := 77518713071130354722638135296 }, { argument := 77505584892307977108944060416, coefficient := 77505584892307977108944060416 }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6
