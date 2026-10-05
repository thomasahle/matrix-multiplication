import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5

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
def constantNumerator : ℤ := 259850363286937421106585096159232
def positiveArguments : Array ℕ := #[
    33, 16777217
  ]
def positiveCoefficients : Array ℕ := #[
    5229058725941446281173900722176, 158456334473261640926378328064
  ]
def positiveScales : Array ℕ := #[
    5, 24
  ]
def negativeArguments : Array ℕ := #[
    2978249531175, 17220616835231, 137734895066399, 1498457104225, 1618306022103, 26815946259909,
    324610121888115, 26816128873263, 1704311128155, 404995908483, 7320124218897, 29280509635847,
    809982759855, 1618306022103, 5755167416121, 101164237407, 2978249351385, 17220614762337,
    137734878503649, 1498456989855, 5755167416121, 190728064987359, 2309070193244985, 95364673743429,
    6063622971429, 7320124218897, 66658051288179, 1066529252447091, 29280162000153, 26815946259909,
    190728064987359, 53643462644631, 2978249531175, 2978249351385, 101164237407, 53643462644631,
    649360691683809, 6705478523043, 13317445695, 29280509635847, 1066529252447091, 133316210535405,
    14640087379983, 324610121888115, 2309070193244985, 649360691683809, 17220616835231, 17220614762337,
    809982759855, 29280162000153, 14640087379983, 404986851213, 26816128873263, 95364673743429,
    6705478523043, 137734895066399, 137734878503649, 1704311128155, 6063622971429, 13317445695,
    1498457104225, 1498456989855
  ]
def negativeCoefficients : Array ℕ := #[
    838302717426005275626700800, 38777381781118210856911372288, 38768926381059306519730847744, 843556357027297810920243200, 455512649882156278971629568, 15096035697964177284931780608,
    182739252997000750181520506880, 15096138500143305694491181056, 479720935105140478370119680, 455984855632653574987579392, 16483454352265136147011731456, 16483461535652345840888971264,
    455979756932437993335029760, 455512649882156278971629568, 1619935614418584743366885376, 455603221889385592491343872, 838302666819619212817858560, 38777377113375887867642904576,
    38768921719059636005313183744, 843556292642711638124789760, 1619935614418584743366885376, 53685177650385358580040597504, 649945478866902102246068060160, 53685538641901971033028558848,
    1706758134665176507087847424, 16483454352265136147011731456, 600402349885372710558596333568, 600402592987556585843711803392, 16483265834154600955417460736, 15096035697964177284931780608,
    53685177650385358580040597504, 15099292398576455843038887936, 838302717426005275626700800, 838302666819619212817858560, 455603221889385592491343872, 15099292398576455843038887936,
    182778785568515609572832968704, 15099395288858659337917169664, 479811547756230529001717760, 16483461535652345840888971264, 600402592987556585843711803392, 600402836089696551032460410880,
    16483273017290734970068795392, 182739252997000750181520506880, 649945478866902102246068060160, 182778785568515609572832968704, 38777381781118210856911372288, 38777377113375887867642904576,
    455979756932437993335029760, 16483265834154600955417460736, 16483273017290734970068795392, 455974658053204326494502912, 15096138500143305694491181056, 53685538641901971033028558848,
    15099395288858659337917169664, 38768926381059306519730847744, 38768921719059636005313183744, 479720935105140478370119680, 1706758134665176507087847424, 479811547756230529001717760,
    843556357027297810920243200, 843556292642711638124789760
  ]
def negativeScales : Array ℕ := #[
    41, 43, 46, 40, 40, 44,
    48, 44, 40, 38, 42, 44,
    39, 40, 42, 36, 41, 43,
    46, 40, 42, 47, 51, 46,
    42, 42, 45, 49, 44, 44,
    47, 45, 41, 41, 36, 45,
    49, 42, 33, 44, 49, 46,
    43, 48, 51, 49, 43, 43,
    39, 44, 43, 38, 44, 46,
    42, 46, 46, 40, 42, 33,
    40, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5044394119358453, 24000000085991322
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41437601773128228, 43969202068288295, 46968887454557282, 40446614923595876, 40557621586235099, 44608156396484437,
    48205701314661748, 44608166221029902, 40632325867460941, 38559116376843695, 42735005269350026, 44735005898067446,
    39559100244924945, 40557621586235099, 42387995035189086, 36557908416461985, 41437601686036080, 43969201894626991,
    46968887281071802, 40446614813481921, 42387995035189086, 47438510475372220, 51036233453463268, 46438520176353806,
    42463317189954267, 42735005269350026, 45921844381624819, 49921844965770240, 44734988769428734, 44608156396484437,
    47438510475372220, 45608467598656316, 41437601773128228, 41437601686036080, 36557908416461985, 45608467598656316,
    49206013383775077, 42608477429500720, 33632598346871778, 44735005898067446, 49921844965770240, 46921845549915319,
    43734989398131369, 48205701314661748, 51036233453463268, 49206013383775077, 43969202068288295, 43969201894626991,
    39559100244924945, 44734988769428734, 43734989398131369, 38559084112259399, 44608166221029902, 46438520176353806,
    42608477429500720, 46968887454557282, 46968887281071802, 40632325867460941, 42463317189954267, 33632598346871778,
    40446614923595876, 40446614813481921
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 62
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
noncomputable def positiveFloor : ℝ := 363283171 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3054392967 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 838302717426005275626700800, coefficient := (-838302717426005275626700800) }, { argument := 38777381781118210856911372288, coefficient := (-38777381781118210856911372288) }, { argument := 38768926381059306519730847744, coefficient := (-38768926381059306519730847744) }, { argument := 843556357027297810920243200, coefficient := (-843556357027297810920243200) }, { argument := 455512649882156278971629568, coefficient := (-455512649882156278971629568) }, { argument := 15096035697964177284931780608, coefficient := (-15096035697964177284931780608) }, { argument := 182739252997000750181520506880, coefficient := (-182739252997000750181520506880) }, { argument := 15096138500143305694491181056, coefficient := (-15096138500143305694491181056) }, { argument := 479720935105140478370119680, coefficient := (-479720935105140478370119680) }, { argument := 455984855632653574987579392, coefficient := (-455984855632653574987579392) }, { argument := 16483454352265136147011731456, coefficient := (-16483454352265136147011731456) }, { argument := 16483461535652345840888971264, coefficient := (-16483461535652345840888971264) }, { argument := 455979756932437993335029760, coefficient := (-455979756932437993335029760) }, { argument := 455512649882156278971629568, coefficient := (-455512649882156278971629568) }, { argument := 1619935614418584743366885376, coefficient := (-1619935614418584743366885376) }, { argument := 455603221889385592491343872, coefficient := (-455603221889385592491343872) }, { argument := 838302666819619212817858560, coefficient := (-838302666819619212817858560) }, { argument := 38777377113375887867642904576, coefficient := (-38777377113375887867642904576) }, { argument := 38768921719059636005313183744, coefficient := (-38768921719059636005313183744) }, { argument := 843556292642711638124789760, coefficient := (-843556292642711638124789760) }, { argument := 1619935614418584743366885376, coefficient := (-1619935614418584743366885376) }, { argument := 53685177650385358580040597504, coefficient := (-53685177650385358580040597504) }, { argument := 649945478866902102246068060160, coefficient := (-649945478866902102246068060160) }, { argument := 53685538641901971033028558848, coefficient := (-53685538641901971033028558848) }, { argument := 1706758134665176507087847424, coefficient := (-1706758134665176507087847424) }, { argument := 16483454352265136147011731456, coefficient := (-16483454352265136147011731456) }, { argument := 600402349885372710558596333568, coefficient := (-600402349885372710558596333568) }, { argument := 600402592987556585843711803392, coefficient := (-600402592987556585843711803392) }, { argument := 16483265834154600955417460736, coefficient := (-16483265834154600955417460736) }, { argument := 15096035697964177284931780608, coefficient := (-15096035697964177284931780608) }, { argument := 53685177650385358580040597504, coefficient := (-53685177650385358580040597504) }, { argument := 15099292398576455843038887936, coefficient := (-15099292398576455843038887936) }, { argument := 838302717426005275626700800, coefficient := (-838302717426005275626700800) }, { argument := 838302666819619212817858560, coefficient := (-838302666819619212817858560) }, { argument := 455603221889385592491343872, coefficient := (-455603221889385592491343872) }, { argument := 15099292398576455843038887936, coefficient := (-15099292398576455843038887936) }, { argument := 182778785568515609572832968704, coefficient := (-182778785568515609572832968704) }, { argument := 15099395288858659337917169664, coefficient := (-15099395288858659337917169664) }, { argument := 479811547756230529001717760, coefficient := (-479811547756230529001717760) }, { argument := 16483461535652345840888971264, coefficient := (-16483461535652345840888971264) }, { argument := 600402592987556585843711803392, coefficient := (-600402592987556585843711803392) }, { argument := 600402836089696551032460410880, coefficient := (-600402836089696551032460410880) }, { argument := 16483273017290734970068795392, coefficient := (-16483273017290734970068795392) }, { argument := 182739252997000750181520506880, coefficient := (-182739252997000750181520506880) }, { argument := 649945478866902102246068060160, coefficient := (-649945478866902102246068060160) }, { argument := 182778785568515609572832968704, coefficient := (-182778785568515609572832968704) }, { argument := 38777381781118210856911372288, coefficient := (-38777381781118210856911372288) }, { argument := 38777377113375887867642904576, coefficient := (-38777377113375887867642904576) }, { argument := 455979756932437993335029760, coefficient := (-455979756932437993335029760) }, { argument := 16483265834154600955417460736, coefficient := (-16483265834154600955417460736) }, { argument := 16483273017290734970068795392, coefficient := (-16483273017290734970068795392) }, { argument := 455974658053204326494502912, coefficient := (-455974658053204326494502912) }, { argument := 15096138500143305694491181056, coefficient := (-15096138500143305694491181056) }, { argument := 53685538641901971033028558848, coefficient := (-53685538641901971033028558848) }, { argument := 15099395288858659337917169664, coefficient := (-15099395288858659337917169664) }, { argument := 38768926381059306519730847744, coefficient := (-38768926381059306519730847744) }, { argument := 38768921719059636005313183744, coefficient := (-38768921719059636005313183744) }, { argument := 479720935105140478370119680, coefficient := (-479720935105140478370119680) }, { argument := 1706758134665176507087847424, coefficient := (-1706758134665176507087847424) }, { argument := 479811547756230529001717760, coefficient := (-479811547756230529001717760) }, { argument := 843556357027297810920243200, coefficient := (-843556357027297810920243200) }, { argument := 843556292642711638124789760, coefficient := (-843556292642711638124789760) }, { argument := 5229058725941446281173900722176, coefficient := 5229058725941446281173900722176 }, { argument := 158456334473261640926378328064, coefficient := 158456334473261640926378328064 }] }

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
def constantNumerator : ℤ := (-252556973285921871064267822727168)
def positiveArguments : Array ℕ := #[
    16777215, 45288027, 161072397, 5662227, 1793533, 127569,
    130630709, 3587025, 535971, 4440597, 53758191, 4440627,
    564609, 355035, 16422859, 8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    158456315583795709447797473280, 427733321560191059836570435584, 1521285777816546386219183898624, 427825776051192681750564175872, 67757761000965147112446623744, 2467543326118698067009474658304,
    2467544327260392435374259961856, 67756986532861956490631577600, 5062102972380253229659717632, 167761011493851983416022532096, 2030927034864836924000843071488, 167762144861807872130873819136,
    5332581235053095028919369728, 3353210768491248976889118720, 155109517788988197449108553728, 155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    23, 25, 27, 22, 20, 16,
    26, 21, 19, 22, 25, 22,
    19, 18, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 15, 1, 15, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2376844875427930127806318510080, 5070602400912917605986812821504, 2376844875427930127806318510080, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 0, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    23999999912549092, 25432626353095736, 27263134039467212, 22432938157707638, 20774372859618859, 16960918262172388,
    26960918847508349, 21774356369586422, 19031795416746646, 22082322216854595, 25679981255464561, 22082331963450611,
    19106892600305326, 18437601729582122, 23969201966206902, 22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3906890600547867, 0, 3906890600547867, 0
  ]

abbrev PositiveTerm := Fin 17
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
noncomputable def positiveFloor : ℝ := 2939142559 / 1000000000000
noncomputable def negativeCeiling : ℝ := 111777037 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158456315583795709447797473280, coefficient := 158456315583795709447797473280 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 427733321560191059836570435584, coefficient := 427733321560191059836570435584 }, { argument := 1521285777816546386219183898624, coefficient := 1521285777816546386219183898624 }, { argument := 427825776051192681750564175872, coefficient := 427825776051192681750564175872 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 67757761000965147112446623744, coefficient := 67757761000965147112446623744 }, { argument := 2467543326118698067009474658304, coefficient := 2467543326118698067009474658304 }, { argument := 2467544327260392435374259961856, coefficient := 2467544327260392435374259961856 }, { argument := 67756986532861956490631577600, coefficient := 67756986532861956490631577600 }, { argument := 5070602400912917605986812821504, coefficient := (-5070602400912917605986812821504) }, { argument := 5062102972380253229659717632, coefficient := 5062102972380253229659717632 }, { argument := 167761011493851983416022532096, coefficient := 167761011493851983416022532096 }, { argument := 2030927034864836924000843071488, coefficient := 2030927034864836924000843071488 }, { argument := 167762144861807872130873819136, coefficient := 167762144861807872130873819136 }, { argument := 5332581235053095028919369728, coefficient := 5332581235053095028919369728 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5
