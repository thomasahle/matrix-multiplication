import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-14019409185341625472278572564480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7613306399, 16877554827, 32088825, 18808054251, 14287725, 4450275,
    3981825, 3981825, 14287725, 563311125, 14287725, 135021195039,
    3981825, 4450275, 14287725, 4450275, 32088825, 3981825,
    3686940117, 7613306399, 622986650475, 311493549951, 15227007321, 622986650475,
    1535022434375, 1117149923, 1837580149463, 497417119, 154933201, 138624443,
    138624443, 497417119, 19611281495, 497417119, 12280253459563, 138624443,
    154933201, 497417119, 154933201, 1117149923, 138624443, 303163792409,
    16877554827, 1535022434375, 767511602923, 33756745933, 32088825, 1117149923,
    279287789, 2005543, 311493549951, 767511602923, 279287789, 918790411867,
    124354417, 38733343, 34656149, 34656149, 124354417, 4902825785,
    124354417, 6140129815679, 34656149, 38733343
  ]
def negativeCoefficients : Array ℕ := #[
    8571820965398453185150976, 152019499259604632164368384, 36995896400065806414643200, 1355263137861882771916455936, 32945250808817725420339200, 5130817748914235926118400,
    36725853360649267681689600, 36725853360649267681689600, 32945250808817725420339200, 649453509796775652753408000, 32945250808817725420339200, 152020350916189865782542336,
    36725853360649267681689600, 5130817748914235926118400, 32945250808817725420339200, 5130817748914235926118400, 36995896400065806414643200, 36725853360649267681689600,
    8302251068529266462294016, 8571820965398453185150976, 350710305867000429359923200, 350710558871909145639911424, 8572043062102926821425152, 350710305867000429359923200,
    6913126463456601649971200000, 1287986170096583244511182848, 66205802211079897162851549184, 1146965786509366100951564288, 178625819210475048508850176, 1278584811190768768273874944,
    1278584811190768768273874944, 1146965786509366100951564288, 22610268168483815350725509120, 1146965786509366100951564288, 6913168113062896396094406656, 1278584811190768768273874944,
    178625819210475048508850176, 1146965786509366100951564288, 178625819210475048508850176, 1287986170096583244511182848, 1278584811190768768273874944, 341332085631349700968841216,
    152019499259604632164368384, 6913126463456601649971200000, 6913129937853109777115119616, 152026868405099306332192768, 36995896400065806414643200, 1287986170096583244511182848,
    1287987591648798424753504256, 36995738449819675276607488, 350710558871909145639911424, 6913129937853109777115119616, 1287987591648798424753504256, 66205826504252891936705216512,
    1146967052417178159269543936, 178626016360052336279683072, 1278586222366690407054573568, 1278586222366690407054573568, 1146967052417178159269543936, 22610293123469782565928304640,
    1146967052417178159269543936, 6913171587474604171980701696, 1278586222366690407054573568, 178626016360052336279683072
  ]
def negativeScales : Array ℕ := #[
    32, 33, 24, 34, 23, 22,
    21, 21, 23, 29, 23, 36,
    21, 22, 23, 22, 24, 21,
    31, 32, 39, 38, 33, 39,
    40, 30, 40, 28, 27, 27,
    27, 28, 34, 28, 43, 27,
    27, 28, 27, 30, 27, 38,
    33, 40, 39, 34, 24, 30,
    28, 20, 38, 39, 28, 39,
    26, 25, 25, 25, 26, 32,
    26, 42, 25, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32825875995984940, 33974386870074734, 24935567635629530, 34130631554373186, 23768272882412886, 22085463057960040,
    21924998392558141, 21924998392558141, 23768272882412886, 29069356723173859, 23768272882412886, 36974394952443193,
    21924998392558141, 22085463057960040, 23768272882412886, 22085463057960040, 24935567635629530, 21924998392558141,
    31779776838890843, 32825875995984940, 39180410292885286, 38180411333655373, 33825913375868552, 39180410292885286,
    40481396879406841, 30057175664386318, 40740944315971290, 28889880922627531, 27207071094869376, 27046606422676130,
    27046606422676130, 28889880922627531, 34190964760083195, 28889880922627531, 43481405571204940, 27046606422676130,
    27207071094869376, 28889880922627531, 27207071094869376, 30057175664386318, 27046606422676130, 38141306502971769,
    33974386870074734, 40481396879406841, 39481397604475792, 34974456803042368, 24935567635629530, 30057175664386318,
    28057177256690060, 20935561476174636, 38180411333655373, 39481397604475792, 28057177256690060, 39740944845345344,
    26889882514931380, 25207072687173119, 25046608014979873, 25046608014979873, 26889882514931380, 32190966352386938,
    26889882514931380, 42481406296272695, 25046608014979873, 25207072687173119
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
noncomputable def negativeCeiling : ℝ := 7045929 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8571820965398453185150976, coefficient := (-8571820965398453185150976) }, { argument := 152019499259604632164368384, coefficient := (-152019499259604632164368384) }, { argument := 36995896400065806414643200, coefficient := (-36995896400065806414643200) }, { argument := 1355263137861882771916455936, coefficient := (-1355263137861882771916455936) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 649453509796775652753408000, coefficient := (-649453509796775652753408000) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 152020350916189865782542336, coefficient := (-152020350916189865782542336) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 36995896400065806414643200, coefficient := (-36995896400065806414643200) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 8302251068529266462294016, coefficient := (-8302251068529266462294016) }, { argument := 8571820965398453185150976, coefficient := (-8571820965398453185150976) }, { argument := 350710305867000429359923200, coefficient := (-350710305867000429359923200) }, { argument := 350710558871909145639911424, coefficient := (-350710558871909145639911424) }, { argument := 8572043062102926821425152, coefficient := (-8572043062102926821425152) }, { argument := 350710305867000429359923200, coefficient := (-350710305867000429359923200) }, { argument := 6913126463456601649971200000, coefficient := (-6913126463456601649971200000) }, { argument := 1287986170096583244511182848, coefficient := (-1287986170096583244511182848) }, { argument := 66205802211079897162851549184, coefficient := (-66205802211079897162851549184) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 22610268168483815350725509120, coefficient := (-22610268168483815350725509120) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 6913168113062896396094406656, coefficient := (-6913168113062896396094406656) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 1287986170096583244511182848, coefficient := (-1287986170096583244511182848) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 341332085631349700968841216, coefficient := (-341332085631349700968841216) }, { argument := 152019499259604632164368384, coefficient := (-152019499259604632164368384) }, { argument := 6913126463456601649971200000, coefficient := (-6913126463456601649971200000) }, { argument := 6913129937853109777115119616, coefficient := (-6913129937853109777115119616) }, { argument := 152026868405099306332192768, coefficient := (-152026868405099306332192768) }, { argument := 36995896400065806414643200, coefficient := (-36995896400065806414643200) }, { argument := 1287986170096583244511182848, coefficient := (-1287986170096583244511182848) }, { argument := 1287987591648798424753504256, coefficient := (-1287987591648798424753504256) }, { argument := 36995738449819675276607488, coefficient := (-36995738449819675276607488) }, { argument := 350710558871909145639911424, coefficient := (-350710558871909145639911424) }, { argument := 6913129937853109777115119616, coefficient := (-6913129937853109777115119616) }, { argument := 1287987591648798424753504256, coefficient := (-1287987591648798424753504256) }, { argument := 66205826504252891936705216512, coefficient := (-66205826504252891936705216512) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 22610293123469782565928304640, coefficient := (-22610293123469782565928304640) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 6913171587474604171980701696, coefficient := (-6913171587474604171980701696) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12424711142947819388865236434944)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    124354417, 38733343, 279287789, 34656149, 151582003957, 18808054251,
    1837580149463, 918790411867, 37618560157, 14287725, 497417119, 124354417,
    892979, 4450275, 154933201, 38733343, 278141, 3981825,
    138624443, 34656149, 248863, 3981825, 138624443, 34656149,
    248863, 14287725, 497417119, 124354417, 892979, 563311125,
    19611281495, 4902825785, 35206795, 14287725, 497417119, 124354417,
    892979, 15227007321, 33756745933, 2005543, 37618560157, 892979,
    278141, 248863, 248863, 892979, 35206795, 892979,
    270055480409, 248863, 278141, 892979, 278141, 2005543,
    248863, 7374078547, 135021195039, 12280253459563, 6140129815679, 270055480409,
    3981825, 138624443, 34656149, 248863
  ]
def negativeCoefficients : Array ℕ := #[
    1146967052417178159269543936, 178626016360052336279683072, 1287987591648798424753504256, 1278586222366690407054573568, 341332328268409125088526336, 1355263137861882771916455936,
    66205802211079897162851549184, 66205826504252891936705216512, 1355351468042238300023422976, 32945250808817725420339200, 1146965786509366100951564288, 1146967052417178159269543936,
    32945110152394163385008128, 5130817748914235926118400, 178625819210475048508850176, 178626016360052336279683072, 5130795843405648396025856, 36725853360649267681689600,
    1278584811190768768273874944, 1278586222366690407054573568, 36725696563324641150500864, 36725853360649267681689600, 1278584811190768768273874944, 1278586222366690407054573568,
    36725696563324641150500864, 32945250808817725420339200, 1146965786509366100951564288, 1146967052417178159269543936, 32945110152394163385008128, 649453509796775652753408000,
    22610268168483815350725509120, 22610293123469782565928304640, 649450737020557073286430720, 32945250808817725420339200, 1146965786509366100951564288, 1146967052417178159269543936,
    32945110152394163385008128, 8572043062102926821425152, 152026868405099306332192768, 36995738449819675276607488, 1355351468042238300023422976, 32945110152394163385008128,
    5130795843405648396025856, 36725696563324641150500864, 36725696563324641150500864, 32945110152394163385008128, 649450737020557073286430720, 32945110152394163385008128,
    152027720117416585339076608, 36725696563324641150500864, 5130795843405648396025856, 32945110152394163385008128, 5130795843405648396025856, 36995738449819675276607488,
    36725696563324641150500864, 8302474349117492143587328, 152020350916189865782542336, 6913168113062896396094406656, 6913171587474604171980701696, 152027720117416585339076608,
    36725853360649267681689600, 1278584811190768768273874944, 1278586222366690407054573568, 36725696563324641150500864
  ]
def negativeScales : Array ℕ := #[
    26, 25, 28, 25, 37, 34,
    40, 39, 35, 23, 28, 26,
    19, 22, 27, 25, 18, 21,
    27, 25, 17, 21, 27, 25,
    17, 23, 28, 26, 19, 29,
    34, 32, 25, 23, 28, 26,
    19, 33, 34, 20, 35, 19,
    18, 17, 17, 19, 25, 19,
    37, 17, 18, 19, 18, 20,
    17, 32, 36, 43, 42, 37,
    21, 27, 25, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26889882514931380, 25207072687173119, 28057177256690060, 25046608014979873, 37141307528516019, 34130631554373186,
    40740944315971290, 39740944845345344, 35130725579922172, 23768272882412886, 28889880922627531, 26889882514931380,
    19768266722958810, 22085463057960040, 27207071094869376, 25207072687173119, 18085456898506008, 21924998392558141,
    27046606422676130, 25046608014979873, 17924992233103382, 21924998392558141, 27046606422676130, 25046608014979873,
    17924992233103382, 23768272882412886, 28889880922627531, 26889882514931380, 19768266722958810, 29069356723173859,
    34190964760083195, 32190966352386938, 25069350563719827, 23768272882412886, 28889880922627531, 26889882514931380,
    19768266722958810, 33825913375868552, 34974456803042368, 20935561476174636, 35130725579922172, 19768266722958810,
    18085456898506008, 17924992233103382, 17924992233103382, 19768266722958810, 25069350563719827, 19768266722958810,
    37974464885547935, 17924992233103382, 18085456898506008, 19768266722958810, 18085456898506008, 20935561476174636,
    17924992233103382, 32779815638183472, 36974394952443193, 43481405571204940, 42481406296272695, 37974464885547935,
    21924998392558141, 27046606422676130, 25046608014979873, 17924992233103382
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
noncomputable def negativeCeiling : ℝ := 24594103 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }, { argument := 1287987591648798424753504256, coefficient := (-1287987591648798424753504256) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 341332328268409125088526336, coefficient := (-341332328268409125088526336) }, { argument := 1355263137861882771916455936, coefficient := (-1355263137861882771916455936) }, { argument := 66205802211079897162851549184, coefficient := (-66205802211079897162851549184) }, { argument := 66205826504252891936705216512, coefficient := (-66205826504252891936705216512) }, { argument := 1355351468042238300023422976, coefficient := (-1355351468042238300023422976) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 649453509796775652753408000, coefficient := (-649453509796775652753408000) }, { argument := 22610268168483815350725509120, coefficient := (-22610268168483815350725509120) }, { argument := 22610293123469782565928304640, coefficient := (-22610293123469782565928304640) }, { argument := 649450737020557073286430720, coefficient := (-649450737020557073286430720) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 8572043062102926821425152, coefficient := (-8572043062102926821425152) }, { argument := 152026868405099306332192768, coefficient := (-152026868405099306332192768) }, { argument := 36995738449819675276607488, coefficient := (-36995738449819675276607488) }, { argument := 1355351468042238300023422976, coefficient := (-1355351468042238300023422976) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 649450737020557073286430720, coefficient := (-649450737020557073286430720) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 152027720117416585339076608, coefficient := (-152027720117416585339076608) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 36995738449819675276607488, coefficient := (-36995738449819675276607488) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 8302474349117492143587328, coefficient := (-8302474349117492143587328) }, { argument := 152020350916189865782542336, coefficient := (-152020350916189865782542336) }, { argument := 6913168113062896396094406656, coefficient := (-6913168113062896396094406656) }, { argument := 6913171587474604171980701696, coefficient := (-6913171587474604171980701696) }, { argument := 152027720117416585339076608, coefficient := (-152027720117416585339076608) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0
