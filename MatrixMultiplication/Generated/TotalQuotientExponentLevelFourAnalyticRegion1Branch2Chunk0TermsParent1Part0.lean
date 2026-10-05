import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

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
def constantNumerator : ℤ := (-33607437099469710592482457157632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37509, 3932751, 126367995, 121813765, 126367995, 121813765,
    42391125, 4510435077, 4129113339, 4510435077, 4129113339, 35,
    35, 35, 35, 35891475, 719265159, 1555036669,
    1158576813, 35891475, 1158576813, 773820201, 73218609, 719265159,
    4306977, 31, 31, 31, 31, 1451,
    1451, 1451, 1451, 395, 395, 395,
    395, 719265159, 3483427449, 719265159, 1966377, 2255218341,
    2064557403, 2255218341, 2064557403, 1451, 1451, 1451,
    1451, 1555036669, 3483427449, 5847430109, 5611029843, 173823725,
    5611029843, 3747639511, 1568942567, 3483427449, 20858847, 35,
    35, 35, 35, 1158576813
  ]
def negativeCoefficients : Array ℕ := #[
    177131244405957522320523264, 18571891507872080083808157696, 291384757859101031257866240, 280883418451249749850849280, 291384757859101031257866240, 280883418451249749850849280,
    200186427871137488959438848000, 10400355190812679389843554304, 9521087126984163598666825728, 10400355190812679389843554304, 9521087126984163598666825728, 169249614746048084458864640,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 82760106719118066135859200, 829256269325563022681309184, 1792835216142299476151762944,
    1335748122446565587432767488, 41380053359559033067929600, 1335748122446565587432767488, 892153950432092752944562176, 84415308853500427458576384, 829256269325563022681309184,
    39724851225176671745212416, 149906801632214017663565824, 149906801632214017663565824, 149906801632214017663565824, 149906801632214017663565824, 7016605457043307729994645504,
    7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504, 1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080,
    1910102794991114096035758080, 829256269325563022681309184, 8032236831379741419082088448, 829256269325563022681309184, 18571905674971528692743798784, 10400358891690709177822347264,
    9521090509655858115155853312, 10400358891690709177822347264, 9521090509655858115155853312, 7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504,
    7016605457043307729994645504, 1792835216142299476151762944, 8032236831379741419082088448, 26966511677406636860072001536, 12938153937970960728940609536, 400810221126733603746611200,
    12938153937970960728940609536, 8641468367492376496776937472, 1808867624987368820301627392, 8032236831379741419082088448, 384777812281664259596746752, 169249614746048084458864640,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 1335748122446565587432767488
  ]
def negativeScales : Array ℕ := #[
    15, 21, 26, 26, 26, 26,
    25, 32, 31, 32, 31, 5,
    5, 5, 5, 25, 29, 30,
    30, 25, 30, 29, 26, 29,
    22, 4, 4, 4, 4, 10,
    10, 10, 10, 8, 8, 8,
    8, 29, 31, 29, 20, 31,
    30, 31, 30, 10, 10, 10,
    10, 30, 31, 32, 32, 27,
    32, 31, 30, 31, 24, 5,
    5, 5, 5, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15194949180424811, 21907107419999676, 26913055885548607, 26860101928719980, 26913055885548607, 26860101928719980,
    25337258918181435, 32070619456681137, 31943184882506053, 32070619456681137, 31943184882506053, 5129283016944967,
    5129283016944967, 5129283016944967, 5129283016944967, 25097137877737747, 29421948481158247, 30534301454639238,
    30109706551240803, 25097137877737747, 30109706551240803, 29527423150716189, 26125707029934518, 29421948481158247,
    22038244188684178, 4954196321574415, 4954196321574415, 4954196321574415, 4954196321574415, 10502831804067043,
    10502831804067043, 10502831804067043, 10502831804067043, 8625708843075807, 8625708843075807, 8625708843075807,
    8625708843075807, 29421948481158247, 31697860369964188, 29421948481158247, 20907108520522911, 31070619970051819,
    30943185395069746, 31070619970051819, 30943185395069746, 10502831804067043, 10502831804067043, 10502831804067043,
    10502831804067043, 30534301454639238, 31697860369964188, 32445155566955335, 32385618439977935, 27373049766474878,
    32385618439977935, 31803335040144038, 30547145395700229, 31697860369964188, 24314156077421308, 5129283016944967,
    5129283016944967, 5129283016944967, 5129283016944967, 30109706551240803
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
noncomputable def negativeCeiling : ℝ := 73814179 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 177131244405957522320523264, coefficient := (-177131244405957522320523264) }, { argument := 18571891507872080083808157696, coefficient := (-18571891507872080083808157696) }, { argument := 291384757859101031257866240, coefficient := (-291384757859101031257866240) }, { argument := 280883418451249749850849280, coefficient := (-280883418451249749850849280) }, { argument := 291384757859101031257866240, coefficient := (-291384757859101031257866240) }, { argument := 280883418451249749850849280, coefficient := (-280883418451249749850849280) }, { argument := 200186427871137488959438848000, coefficient := (-200186427871137488959438848000) }, { argument := 10400355190812679389843554304, coefficient := (-10400355190812679389843554304) }, { argument := 9521087126984163598666825728, coefficient := (-9521087126984163598666825728) }, { argument := 10400355190812679389843554304, coefficient := (-10400355190812679389843554304) }, { argument := 9521087126984163598666825728, coefficient := (-9521087126984163598666825728) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 82760106719118066135859200, coefficient := (-82760106719118066135859200) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 1792835216142299476151762944, coefficient := (-1792835216142299476151762944) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 41380053359559033067929600, coefficient := (-41380053359559033067929600) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 892153950432092752944562176, coefficient := (-892153950432092752944562176) }, { argument := 84415308853500427458576384, coefficient := (-84415308853500427458576384) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 39724851225176671745212416, coefficient := (-39724851225176671745212416) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 8032236831379741419082088448, coefficient := (-8032236831379741419082088448) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 18571905674971528692743798784, coefficient := (-18571905674971528692743798784) }, { argument := 10400358891690709177822347264, coefficient := (-10400358891690709177822347264) }, { argument := 9521090509655858115155853312, coefficient := (-9521090509655858115155853312) }, { argument := 10400358891690709177822347264, coefficient := (-10400358891690709177822347264) }, { argument := 9521090509655858115155853312, coefficient := (-9521090509655858115155853312) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1792835216142299476151762944, coefficient := (-1792835216142299476151762944) }, { argument := 8032236831379741419082088448, coefficient := (-8032236831379741419082088448) }, { argument := 26966511677406636860072001536, coefficient := (-26966511677406636860072001536) }, { argument := 12938153937970960728940609536, coefficient := (-12938153937970960728940609536) }, { argument := 400810221126733603746611200, coefficient := (-400810221126733603746611200) }, { argument := 12938153937970960728940609536, coefficient := (-12938153937970960728940609536) }, { argument := 8641468367492376496776937472, coefficient := (-8641468367492376496776937472) }, { argument := 1808867624987368820301627392, coefficient := (-1808867624987368820301627392) }, { argument := 8032236831379741419082088448, coefficient := (-8032236831379741419082088448) }, { argument := 384777812281664259596746752, coefficient := (-384777812281664259596746752) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }] }

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
def constantNumerator : ℤ := (-8177517890669083445541084332032)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5611029843, 1158576813, 52967675, 4434937605, 2217469605, 26483035,
    35, 35, 35, 35, 15, 15,
    15, 15, 35891475, 173823725, 35891475, 35,
    35, 35, 35, 395, 395, 395,
    395, 1158576813, 5611029843, 1158576813, 15, 15,
    15, 15, 773820201, 3747639511, 773820201, 48413445,
    4053615867, 2026808667, 24205989, 37509, 63183195, 60906149,
    63183195, 60906149, 73218609, 719265159, 1568942567, 1158576813,
    35891475, 1158576813, 773820201, 18663567, 719265159, 4306977,
    31, 31, 31, 31, 719265159, 3483427449,
    719265159, 52967675, 4434937605, 2217469605
  ]
def negativeCoefficients : Array ℕ := #[
    12938153937970960728940609536, 1335748122446565587432767488, 122135143113052946799001600, 10226269872788172788685864960, 10226273573666202576664657920, 122131442235023158820208640,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 145071098353755500964741120, 145071098353755500964741120,
    145071098353755500964741120, 145071098353755500964741120, 41380053359559033067929600, 400810221126733603746611200, 41380053359559033067929600, 169249614746048084458864640,
    169249614746048084458864640, 169249614746048084458864640, 169249614746048084458864640, 1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080,
    1910102794991114096035758080, 1335748122446565587432767488, 12938153937970960728940609536, 1335748122446565587432767488, 145071098353755500964741120, 145071098353755500964741120,
    145071098353755500964741120, 145071098353755500964741120, 892153950432092752944562176, 8641468367492376496776937472, 892153950432092752944562176, 111633803705201665391984640,
    9347001808959656997509136384, 9347005191631351513998163968, 111630421033507148902957056, 177131244405957522320523264, 291381056981071243279073280, 280880035779555233361821696,
    291381056981071243279073280, 280880035779555233361821696, 84415308853500427458576384, 829256269325563022681309184, 1808867624987368820301627392, 1335748122446565587432767488,
    41380053359559033067929600, 1335748122446565587432767488, 892153950432092752944562176, 86070510987882788781293568, 829256269325563022681309184, 39724851225176671745212416,
    149906801632214017663565824, 149906801632214017663565824, 149906801632214017663565824, 149906801632214017663565824, 829256269325563022681309184, 8032236831379741419082088448,
    829256269325563022681309184, 122135143113052946799001600, 10226269872788172788685864960, 10226273573666202576664657920
  ]
def negativeScales : Array ℕ := #[
    32, 30, 25, 32, 31, 24,
    5, 5, 5, 5, 3, 3,
    3, 3, 25, 27, 25, 5,
    5, 5, 5, 8, 8, 8,
    8, 30, 32, 30, 3, 3,
    3, 3, 29, 31, 29, 25,
    31, 30, 24, 15, 25, 25,
    25, 25, 26, 29, 30, 30,
    25, 30, 29, 24, 29, 22,
    4, 4, 4, 4, 29, 31,
    29, 25, 32, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32385618439977935, 30109706551240803, 25658608847602671, 32046266661423470, 31046267183533436, 24658565131116628,
    5129283016944967, 5129283016944967, 5129283016944967, 5129283016944967, 3906890600547867, 3906890600547867,
    3906890600547867, 3906890600547867, 25097137877737747, 27373049766474878, 25097137877737747, 5129283016944967,
    5129283016944967, 5129283016944967, 5129283016944967, 8625708843075807, 8625708843075807, 8625708843075807,
    8625708843075807, 30109706551240803, 32385618439977935, 30109706551240803, 3906890600547867, 3906890600547867,
    3906890600547867, 3906890600547867, 29527423150716189, 31803335040144038, 29527423150716189, 25528904421240604,
    31916562240947312, 30916562763057331, 24528860704754590, 15194949180424811, 25913037561759656, 25860084554275862,
    25913037561759656, 25860084554275862, 26125707029934518, 29421948481158247, 30547145395700229, 30109706551240803,
    25097137877737747, 30109706551240803, 29527423150716189, 24153721406104114, 29421948481158247, 22038244188684178,
    4954196321574415, 4954196321574415, 4954196321574415, 4954196321574415, 29421948481158247, 31697860369964188,
    29421948481158247, 25658608847602671, 32046266661423470, 31046267183533436
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
noncomputable def negativeCeiling : ℝ := 46040769 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12938153937970960728940609536, coefficient := (-12938153937970960728940609536) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 122135143113052946799001600, coefficient := (-122135143113052946799001600) }, { argument := 10226269872788172788685864960, coefficient := (-10226269872788172788685864960) }, { argument := 10226273573666202576664657920, coefficient := (-10226273573666202576664657920) }, { argument := 122131442235023158820208640, coefficient := (-122131442235023158820208640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 41380053359559033067929600, coefficient := (-41380053359559033067929600) }, { argument := 400810221126733603746611200, coefficient := (-400810221126733603746611200) }, { argument := 41380053359559033067929600, coefficient := (-41380053359559033067929600) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 12938153937970960728940609536, coefficient := (-12938153937970960728940609536) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 145071098353755500964741120, coefficient := (-145071098353755500964741120) }, { argument := 892153950432092752944562176, coefficient := (-892153950432092752944562176) }, { argument := 8641468367492376496776937472, coefficient := (-8641468367492376496776937472) }, { argument := 892153950432092752944562176, coefficient := (-892153950432092752944562176) }, { argument := 111633803705201665391984640, coefficient := (-111633803705201665391984640) }, { argument := 9347001808959656997509136384, coefficient := (-9347001808959656997509136384) }, { argument := 9347005191631351513998163968, coefficient := (-9347005191631351513998163968) }, { argument := 111630421033507148902957056, coefficient := (-111630421033507148902957056) }, { argument := 177131244405957522320523264, coefficient := (-177131244405957522320523264) }, { argument := 291381056981071243279073280, coefficient := (-291381056981071243279073280) }, { argument := 280880035779555233361821696, coefficient := (-280880035779555233361821696) }, { argument := 291381056981071243279073280, coefficient := (-291381056981071243279073280) }, { argument := 280880035779555233361821696, coefficient := (-280880035779555233361821696) }, { argument := 84415308853500427458576384, coefficient := (-84415308853500427458576384) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 1808867624987368820301627392, coefficient := (-1808867624987368820301627392) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 41380053359559033067929600, coefficient := (-41380053359559033067929600) }, { argument := 1335748122446565587432767488, coefficient := (-1335748122446565587432767488) }, { argument := 892153950432092752944562176, coefficient := (-892153950432092752944562176) }, { argument := 86070510987882788781293568, coefficient := (-86070510987882788781293568) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 39724851225176671745212416, coefficient := (-39724851225176671745212416) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 149906801632214017663565824, coefficient := (-149906801632214017663565824) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 8032236831379741419082088448, coefficient := (-8032236831379741419082088448) }, { argument := 829256269325563022681309184, coefficient := (-829256269325563022681309184) }, { argument := 122135143113052946799001600, coefficient := (-122135143113052946799001600) }, { argument := 10226269872788172788685864960, coefficient := (-10226269872788172788685864960) }, { argument := 10226273573666202576664657920, coefficient := (-10226273573666202576664657920) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
