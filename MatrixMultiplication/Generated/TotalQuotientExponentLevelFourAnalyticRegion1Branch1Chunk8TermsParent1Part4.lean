import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-44936541146608780289699594895360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5415, 5415, 10545, 326895, 10545, 855,
    13965, 5342157, 1859872083, 80465, 67086776537, 3135,
    5225, 159885, 5225, 3135, 2561295, 164065,
    7439493179, 159885, 5225, 164065, 5225, 159885,
    5225, 5342157, 644324367, 12680180635, 6340089899, 644324367,
    26163, 78489, 165699, 427329, 357561, 10002987,
    305235, 357561, 322677, 165699, 165699, 322677,
    10002987, 322677, 26163, 427329, 5299917, 1857422163,
    156695, 67086213337, 6105, 10175, 311355, 10175,
    6105, 4987785, 319495, 7429693499, 311355, 10175,
    319495, 10175, 311355, 10175
  ]
def negativeCoefficients : Array ℕ := #[
    51143229009478257664327680, 51143229009478257664327680, 49797354561860408778424320, 1543717991417672672131153920, 49797354561860408778424320, 64601973485656746523361280,
    65947847933274595409264640, 197090805961151994264551424, 17154292162469044650522968064, 1519940876176424008480194560, 154691574688522718238132404224, 947495611122965615675965440,
    49348729745987792483123200, 1510071130227226449983569920, 1579159351871609359459942400, 947495611122965615675965440, 24190747321483215875226992640, 1549550114024016683970068480,
    17154303338890110309297553408, 1510071130227226449983569920, 49348729745987792483123200, 1549550114024016683970068480, 49348729745987792483123200, 1510071130227226449983569920,
    1579159351871609359459942400, 197090805961151994264551424, 742855418656494261677064192, 29238505872781608626967019520, 29238503942791009915105181696, 742855418656494261677064192,
    1976820388661096443614855168, 1482615291495822332711141376, 1564982807690034684528427008, 2018004146758202619523497984, 27016545311701651396069687296, 47237770537380783767213309952,
    1441431533398716156802498560, 27016545311701651396069687296, 1523799049592928508619784192, 1564982807690034684528427008, 1564982807690034684528427008, 1523799049592928508619784192,
    47237770537380783767213309952, 1523799049592928508619784192, 1976820388661096443614855168, 2018004146758202619523497984, 195532425021805011344031744, 17131695638848513398175432704,
    1479942432066518113520189440, 154690276037739929085698637824, 922561516093413888947650560, 48050078963198640049356800, 1470332416273878385510318080, 1537602526822356481579417600,
    922561516093413888947650560, 23554148707759973352194703360, 1508772479444437297549803520, 17131706815269579056950018048, 1470332416273878385510318080, 48050078963198640049356800,
    1508772479444437297549803520, 48050078963198640049356800, 1470332416273878385510318080, 1537602526822356481579417600
  ]
def negativeScales : Array ℕ := #[
    12, 12, 13, 18, 13, 9,
    13, 22, 30, 16, 35, 11,
    12, 17, 12, 11, 21, 17,
    32, 17, 12, 17, 12, 17,
    12, 22, 29, 33, 32, 29,
    14, 16, 17, 18, 18, 23,
    18, 18, 18, 17, 17, 18,
    23, 18, 14, 18, 22, 30,
    17, 35, 12, 13, 18, 13,
    12, 22, 18, 32, 18, 13,
    18, 13, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12402745622495697, 12402745622495697, 13364271474681056, 18318467785067930, 13364271474681056, 9739780609952834,
    13769527953509885, 22348990945108702, 30792556254601274, 16296073767663147, 35965309387417924, 11614249727697750,
    12351215321855609, 17286675069660898, 12351215321855609, 11614249727697750, 21288441995835085, 17323907975859873,
    32792557194550415, 17286675069660898, 12351215321855609, 17323907975859873, 12351215321855609, 17286675069660898,
    12351215321855609, 22348990945108702, 29263211914599086, 33561856246353039, 32561856151122867, 29263211914599086,
    14675240357618530, 16260202858299706, 17338205370300980, 18704987701053965, 18447829861475521, 23253927532873219,
    18219560873802360, 18447829861475521, 18299731222486344, 17338205370300980, 17338205370300980, 18299731222486344,
    23253927532873219, 18299731222486344, 14675240357618530, 18704987701053965, 22337538335674348, 30790654609075221,
    17257599619848511, 35965297275799493, 12575775579877617, 13312741174040972, 18248200921846262, 13312741174040972,
    12575775579877617, 22249967848020450, 18285433828045237, 32790655550264144, 18248200921846262, 13312741174040972,
    18285433828045237, 13312741174040972, 18248200921846262, 13312741174040972
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
noncomputable def negativeCeiling : ℝ := 245051321 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 197090805961151994264551424, coefficient := (-197090805961151994264551424) }, { argument := 17154292162469044650522968064, coefficient := (-17154292162469044650522968064) }, { argument := 1519940876176424008480194560, coefficient := (-1519940876176424008480194560) }, { argument := 154691574688522718238132404224, coefficient := (-154691574688522718238132404224) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 24190747321483215875226992640, coefficient := (-24190747321483215875226992640) }, { argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 17154303338890110309297553408, coefficient := (-17154303338890110309297553408) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 197090805961151994264551424, coefficient := (-197090805961151994264551424) }, { argument := 742855418656494261677064192, coefficient := (-742855418656494261677064192) }, { argument := 29238505872781608626967019520, coefficient := (-29238505872781608626967019520) }, { argument := 29238503942791009915105181696, coefficient := (-29238503942791009915105181696) }, { argument := 742855418656494261677064192, coefficient := (-742855418656494261677064192) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 1482615291495822332711141376, coefficient := (-1482615291495822332711141376) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 195532425021805011344031744, coefficient := (-195532425021805011344031744) }, { argument := 17131695638848513398175432704, coefficient := (-17131695638848513398175432704) }, { argument := 1479942432066518113520189440, coefficient := (-1479942432066518113520189440) }, { argument := 154690276037739929085698637824, coefficient := (-154690276037739929085698637824) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 23554148707759973352194703360, coefficient := (-23554148707759973352194703360) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 17131706815269579056950018048, coefficient := (-17131706815269579056950018048) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }] }

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


end Parent1

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-633119452286067914885844812431360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5299917, 855, 2565, 5415, 13965, 11685,
    326895, 9975, 11685, 10545, 5415, 5415,
    10545, 326895, 10545, 855, 13965, 165913443,
    58344097917, 4857545, 2108673856663, 189255, 315425, 9652005,
    315425, 189255, 154621335, 9904345, 233376544021, 9652005,
    315425, 9904345, 315425, 9652005, 315425, 165913443,
    6527705349, 128470851637, 64235421539, 6527705349, 5299917, 1857422163,
    156695, 67086213337, 6105, 10175, 311355, 10175,
    6105, 4987785, 319495, 7429693499, 311355, 10175,
    319495, 10175, 311355, 10175, 5299917, 13217718801,
    260115329113, 130057656011, 13217718801, 16684969731
  ]
def negativeCoefficients : Array ℕ := #[
    195532425021805011344031744, 2067263151541015888747560960, 1550447363655761916560670720, 1636583328303304245258485760, 2110331133864787053096468480, 28252596404393883812883333120,
    49398975725365525508196925440, 1507379381331990752211763200, 28252596404393883812883333120, 1593515345979533080909578240, 1636583328303304245258485760, 1636583328303304245258485760,
    1593515345979533080909578240, 49398975725365525508196925440, 1593515345979533080909578240, 2067263151541015888747560960, 2110331133864787053096468480, 6121125642817994981193547776,
    538129321243174772451034791936, 45878215394062061519125872640, 4862270871098057468876398002176, 28599406998895830557377167360, 1489552447859157841530060800, 45580304904490229950819860480,
    47665678331493050928961945600, 28599406998895830557377167360, 730178609940559173918035804160, 46771946862777556224043909120, 538129672545274755184949460992, 45580304904490229950819860480,
    1489552447859157841530060800, 46771946862777556224043909120, 1489552447859157841530060800, 45580304904490229950819860480, 47665678331493050928961945600, 6121125642817994981193547776,
    15051863745198486294519349248, 592467230269812199472232398848, 592467190798391567752219328512, 15051863745198486294519349248, 195532425021805011344031744, 17131695638848513398175432704,
    1479942432066518113520189440, 154690276037739929085698637824, 922561516093413888947650560, 48050078963198640049356800, 1470332416273878385510318080, 1537602526822356481579417600,
    922561516093413888947650560, 23554148707759973352194703360, 1508772479444437297549803520, 17131706815269579056950018048, 1470332416273878385510318080, 48050078963198640049356800,
    1508772479444437297549803520, 48050078963198640049356800, 1470332416273878385510318080, 1537602526822356481579417600, 195532425021805011344031744, 15238992247519129388005195776,
    599785113224530293670937624576, 599785073815367423199694290944, 15238992247519129388005195776, 76945841626336875399635533824
  ]
def negativeScales : Array ℕ := #[
    22, 9, 11, 12, 13, 13,
    18, 13, 13, 13, 12, 12,
    13, 18, 13, 9, 13, 27,
    35, 22, 40, 17, 18, 23,
    18, 17, 27, 23, 37, 23,
    18, 23, 18, 23, 18, 27,
    32, 36, 35, 32, 22, 30,
    17, 35, 12, 13, 18, 13,
    12, 22, 18, 32, 18, 13,
    18, 13, 18, 13, 22, 33,
    37, 36, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22337538335674348, 9739780609952834, 11324743110494417, 12402745622495697, 13769527953509885, 13512370113670596,
    18318467785067930, 13284101125997071, 13512370113670596, 13364271474681056, 12402745622495697, 12402745622495697,
    13364271474681056, 18318467785067930, 13364271474681056, 9739780609952834, 13769527953509885, 27305855543305370,
    35763867669607796, 22211795930235387, 40939473121699943, 17529971890262358, 18266937484427848, 23202397232233137,
    18266937484427848, 17529971890262358, 27204164158407325, 23239630138432112, 37763868611429056, 23202397232233137,
    18266937484427848, 23239630138432112, 18266937484427848, 23202397232233137, 18266937484427848, 27305855543305370,
    32603928791643524, 36902650116172859, 35902650020057451, 32603928791643524, 22337538335674348, 30790654609075221,
    17257599619848511, 35965297275799493, 12575775579877617, 13312741174040972, 18248200921846262, 13312741174040972,
    12575775579877617, 22249967848020450, 18285433828045237, 32790655550264144, 18248200921846262, 13312741174040972,
    18285433828045237, 13312741174040972, 18248200921846262, 13312741174040972, 22337538335674348, 33621754157615546,
    37920360472695133, 36920360377902163, 33621754157615546, 33957830030024671
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
noncomputable def negativeCeiling : ℝ := 892931849 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 195532425021805011344031744, coefficient := (-195532425021805011344031744) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 1550447363655761916560670720, coefficient := (-1550447363655761916560670720) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 2110331133864787053096468480, coefficient := (-2110331133864787053096468480) }, { argument := 28252596404393883812883333120, coefficient := (-28252596404393883812883333120) }, { argument := 49398975725365525508196925440, coefficient := (-49398975725365525508196925440) }, { argument := 1507379381331990752211763200, coefficient := (-1507379381331990752211763200) }, { argument := 28252596404393883812883333120, coefficient := (-28252596404393883812883333120) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 1636583328303304245258485760, coefficient := (-1636583328303304245258485760) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 49398975725365525508196925440, coefficient := (-49398975725365525508196925440) }, { argument := 1593515345979533080909578240, coefficient := (-1593515345979533080909578240) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 2110331133864787053096468480, coefficient := (-2110331133864787053096468480) }, { argument := 6121125642817994981193547776, coefficient := (-6121125642817994981193547776) }, { argument := 538129321243174772451034791936, coefficient := (-538129321243174772451034791936) }, { argument := 45878215394062061519125872640, coefficient := (-45878215394062061519125872640) }, { argument := 4862270871098057468876398002176, coefficient := (-4862270871098057468876398002176) }, { argument := 28599406998895830557377167360, coefficient := (-28599406998895830557377167360) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 47665678331493050928961945600, coefficient := (-47665678331493050928961945600) }, { argument := 28599406998895830557377167360, coefficient := (-28599406998895830557377167360) }, { argument := 730178609940559173918035804160, coefficient := (-730178609940559173918035804160) }, { argument := 46771946862777556224043909120, coefficient := (-46771946862777556224043909120) }, { argument := 538129672545274755184949460992, coefficient := (-538129672545274755184949460992) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 46771946862777556224043909120, coefficient := (-46771946862777556224043909120) }, { argument := 1489552447859157841530060800, coefficient := (-1489552447859157841530060800) }, { argument := 45580304904490229950819860480, coefficient := (-45580304904490229950819860480) }, { argument := 47665678331493050928961945600, coefficient := (-47665678331493050928961945600) }, { argument := 6121125642817994981193547776, coefficient := (-6121125642817994981193547776) }, { argument := 15051863745198486294519349248, coefficient := (-15051863745198486294519349248) }, { argument := 592467230269812199472232398848, coefficient := (-592467230269812199472232398848) }, { argument := 592467190798391567752219328512, coefficient := (-592467190798391567752219328512) }, { argument := 15051863745198486294519349248, coefficient := (-15051863745198486294519349248) }, { argument := 195532425021805011344031744, coefficient := (-195532425021805011344031744) }, { argument := 17131695638848513398175432704, coefficient := (-17131695638848513398175432704) }, { argument := 1479942432066518113520189440, coefficient := (-1479942432066518113520189440) }, { argument := 154690276037739929085698637824, coefficient := (-154690276037739929085698637824) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 23554148707759973352194703360, coefficient := (-23554148707759973352194703360) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 17131706815269579056950018048, coefficient := (-17131706815269579056950018048) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }, { argument := 195532425021805011344031744, coefficient := (-195532425021805011344031744) }, { argument := 15238992247519129388005195776, coefficient := (-15238992247519129388005195776) }, { argument := 599785113224530293670937624576, coefficient := (-599785113224530293670937624576) }, { argument := 599785073815367423199694290944, coefficient := (-599785073815367423199694290944) }, { argument := 15238992247519129388005195776, coefficient := (-15238992247519129388005195776) }, { argument := 76945841626336875399635533824, coefficient := (-76945841626336875399635533824) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
