import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 6, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6

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
def constantNumerator : ℤ := (-3005352205864792678112425934848)
def positiveArguments : Array ℕ := #[
    7, 18066645, 2016525, 18067851, 861957, 32690483,
    130787469, 3438227, 126633, 3390987, 86607873, 6769713,
    125235
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 170634637611808922703589539840, 609457284599597524131092889600, 170646027959765604287844974592, 32563814771798966235694104576, 1235011529824159424594883641344,
    1235252719969905508854527950848, 32473135890594903308300713984, 2392029739300927129383862272, 64053933410586758457021431808, 817988233215661816445682057216, 63938131539693829017091178496,
    2365622265928720073348874240
  ]
def positiveScales : Array ℕ := #[
    2, 24, 20, 24, 19, 24,
    26, 21, 16, 21, 26, 22,
    16
  ]
def negativeArguments : Array ℕ := #[
    762287342859, 10204552254861, 65202749455059, 20371826805093, 376894541205, 23084132679,
    7045469322789, 28187132788893, 737252761071, 762287342859, 340554404589, 762375807885,
    340554404589, 36480830716743, 931402532836083, 72830472277689, 1347257018415, 7045469322789,
    534331890497777, 1068872698918143, 28102820536459, 10204552254861, 36480830716743, 2551484595147,
    762375807885, 2551484595147, 260825461965249, 10187319088113, 94235771535, 28187132788893,
    1068872698918143, 534540861904185, 14054030995449, 65202749455059, 931402532836083, 260825461965249,
    737252761071, 28102820536459, 14054030995449, 183935436901, 20371826805093, 72830472277689,
    10187319088113, 376894541205, 1347257018415, 94235771535, 3, 1,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    214564812078064870310805504, 5744652216559344291132997632, 73411769537333880881273634816, 5734159475517069802768171008, 212172764416101506309160960, 207923382662630979108077568,
    7932493254190700300479758336, 7933972545293825280791543808, 207518203752326557467672576, 214564812078064870310805504, 766860344803200766492803072, 214589712769197927888322560,
    766860344803200766492803072, 20536881952761239914011426816, 262166506238282472734167400448, 20499955488188588717437353984, 758438275763259933437460480, 7932493254190700300479758336,
    300802112867245146203880423424, 300860918034640323611939831808, 7910240756003542181141807104, 5744652216559344291132997632, 20536881952761239914011426816, 5745432535972795023366291456,
    214589712769197927888322560, 5745432535972795023366291456, 73415840832214554607399993344, 5734950806141255988340064256, 212200092784998596927815680, 7933972545293825280791543808,
    300860918034640323611939831808, 300919753310748915863880990720, 7911716094269689670651609088, 73411769537333880881273634816, 262166506238282472734167400448, 73415840832214554607399993344,
    207518203752326557467672576, 7910240756003542181141807104, 7911716094269689670651609088, 207092891271893244889268224, 5734159475517069802768171008, 20499955488188588717437353984,
    5734950806141255988340064256, 212172764416101506309160960, 758438275763259933437460480, 212200092784998596927815680, 950737950171172051122527404032, 2535301200456458802993406410752,
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    39, 43, 45, 44, 38, 34,
    42, 44, 39, 39, 38, 39,
    38, 45, 49, 46, 40, 42,
    48, 49, 44, 43, 45, 41,
    39, 41, 47, 43, 36, 44,
    49, 48, 43, 45, 49, 47,
    39, 44, 43, 37, 44, 46,
    43, 38, 40, 36, 1, 0,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24106825284899160, 20943439860508680, 24106921585687191, 19717256374563377, 24962367356418682,
    26962649078362986, 21713233367468281, 16950293887501648, 21693273822845735, 26367994841840005, 22690663241783553,
    16934278289168840
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39471543965333107, 43214278116164766, 45889998038165437, 44211640590593417, 38455369943476745, 34426182477093198,
    42679832951275968, 44680101967195958, 39423368364067317, 39471543965333107, 38309094335275786, 39471711383368210,
    38309094335275786, 45052203815485735, 49726398133953690, 46049607434038365, 40293162240986431, 42679832951275968,
    48924729459193518, 49925011470649411, 44675780167216520, 43214278116164766, 45052203815485735, 41214474069976086,
    39471711383368210, 41214474069976086, 47890078045424427, 43211839672953076, 36455555754146155, 44680101967195958,
    49925011470649411, 48925293571339696, 43676049219044764, 45889998038165437, 49726398133953690, 47890078045424427,
    39423368364067317, 44675780167216520, 43676049219044764, 37420408499129112, 44211640590593417, 46049607434038365,
    43211839672953076, 38455369943476745, 40293162240986431, 36455555754146155, 1584962500724866, 0,
    1584962500724866
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 352657219 / 250000000000
noncomputable def negativeCeiling : ℝ := 267340149 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 214564812078064870310805504, coefficient := (-214564812078064870310805504) }, { argument := 5744652216559344291132997632, coefficient := (-5744652216559344291132997632) }, { argument := 73411769537333880881273634816, coefficient := (-73411769537333880881273634816) }, { argument := 5734159475517069802768171008, coefficient := (-5734159475517069802768171008) }, { argument := 212172764416101506309160960, coefficient := (-212172764416101506309160960) }, { argument := 207923382662630979108077568, coefficient := (-207923382662630979108077568) }, { argument := 7932493254190700300479758336, coefficient := (-7932493254190700300479758336) }, { argument := 7933972545293825280791543808, coefficient := (-7933972545293825280791543808) }, { argument := 207518203752326557467672576, coefficient := (-207518203752326557467672576) }, { argument := 214564812078064870310805504, coefficient := (-214564812078064870310805504) }, { argument := 766860344803200766492803072, coefficient := (-766860344803200766492803072) }, { argument := 214589712769197927888322560, coefficient := (-214589712769197927888322560) }, { argument := 766860344803200766492803072, coefficient := (-766860344803200766492803072) }, { argument := 20536881952761239914011426816, coefficient := (-20536881952761239914011426816) }, { argument := 262166506238282472734167400448, coefficient := (-262166506238282472734167400448) }, { argument := 20499955488188588717437353984, coefficient := (-20499955488188588717437353984) }, { argument := 758438275763259933437460480, coefficient := (-758438275763259933437460480) }, { argument := 7932493254190700300479758336, coefficient := (-7932493254190700300479758336) }, { argument := 300802112867245146203880423424, coefficient := (-300802112867245146203880423424) }, { argument := 300860918034640323611939831808, coefficient := (-300860918034640323611939831808) }, { argument := 7910240756003542181141807104, coefficient := (-7910240756003542181141807104) }, { argument := 5744652216559344291132997632, coefficient := (-5744652216559344291132997632) }, { argument := 20536881952761239914011426816, coefficient := (-20536881952761239914011426816) }, { argument := 5745432535972795023366291456, coefficient := (-5745432535972795023366291456) }, { argument := 214589712769197927888322560, coefficient := (-214589712769197927888322560) }, { argument := 5745432535972795023366291456, coefficient := (-5745432535972795023366291456) }, { argument := 73415840832214554607399993344, coefficient := (-73415840832214554607399993344) }, { argument := 5734950806141255988340064256, coefficient := (-5734950806141255988340064256) }, { argument := 212200092784998596927815680, coefficient := (-212200092784998596927815680) }, { argument := 7933972545293825280791543808, coefficient := (-7933972545293825280791543808) }, { argument := 300860918034640323611939831808, coefficient := (-300860918034640323611939831808) }, { argument := 300919753310748915863880990720, coefficient := (-300919753310748915863880990720) }, { argument := 7911716094269689670651609088, coefficient := (-7911716094269689670651609088) }, { argument := 73411769537333880881273634816, coefficient := (-73411769537333880881273634816) }, { argument := 262166506238282472734167400448, coefficient := (-262166506238282472734167400448) }, { argument := 73415840832214554607399993344, coefficient := (-73415840832214554607399993344) }, { argument := 207518203752326557467672576, coefficient := (-207518203752326557467672576) }, { argument := 7910240756003542181141807104, coefficient := (-7910240756003542181141807104) }, { argument := 7911716094269689670651609088, coefficient := (-7911716094269689670651609088) }, { argument := 207092891271893244889268224, coefficient := (-207092891271893244889268224) }, { argument := 5734159475517069802768171008, coefficient := (-5734159475517069802768171008) }, { argument := 20499955488188588717437353984, coefficient := (-20499955488188588717437353984) }, { argument := 5734950806141255988340064256, coefficient := (-5734950806141255988340064256) }, { argument := 212172764416101506309160960, coefficient := (-212172764416101506309160960) }, { argument := 758438275763259933437460480, coefficient := (-758438275763259933437460480) }, { argument := 212200092784998596927815680, coefficient := (-212200092784998596927815680) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 170634637611808922703589539840, coefficient := 170634637611808922703589539840 }, { argument := 609457284599597524131092889600, coefficient := 609457284599597524131092889600 }, { argument := 170646027959765604287844974592, coefficient := 170646027959765604287844974592 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 32563814771798966235694104576, coefficient := 32563814771798966235694104576 }, { argument := 1235011529824159424594883641344, coefficient := 1235011529824159424594883641344 }, { argument := 1235252719969905508854527950848, coefficient := 1235252719969905508854527950848 }, { argument := 32473135890594903308300713984, coefficient := 32473135890594903308300713984 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 2392029739300927129383862272, coefficient := 2392029739300927129383862272 }, { argument := 64053933410586758457021431808, coefficient := 64053933410586758457021431808 }, { argument := 817988233215661816445682057216, coefficient := 817988233215661816445682057216 }, { argument := 63938131539693829017091178496, coefficient := 63938131539693829017091178496 }, { argument := 2365622265928720073348874240, coefficient := 2365622265928720073348874240 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6
