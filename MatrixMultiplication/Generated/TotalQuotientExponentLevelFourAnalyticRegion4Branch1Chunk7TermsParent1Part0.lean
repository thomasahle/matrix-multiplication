import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7

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
def constantNumerator : ℤ := (-5993427737036357796373096038400)
def positiveArguments : Array ℕ := #[
    17, 25165833, 25165815, 86882303, 296010067, 43434839,
    6514515, 228366511, 114185465, 1627523, 5985, 1919827,
    84921627, 959919, 191489
  ]
def positiveCoefficients : Array ℕ := #[
    5387515050969974956360988622848, 475369145090779408868491395072, 475368805080392642254036008960, 820580151283449649917671243776, 2795736037985596063944764555264, 820460911529757191376025419776,
    61527854576303093578601594880, 2156860714712564290519209869312, 2156902450987539892443608514560, 61486080522395628697041240064, 1808855257598388902654115840, 72529013421665458893394804736,
    802062090031115800919654006784, 72529428989915951422173609984, 1808562470876450984650866688
  ]
def positiveScales : Array ℕ := #[
    4, 24, 24, 26, 28, 25,
    22, 27, 26, 20, 12, 20,
    26, 19, 17
  ]
def negativeArguments : Array ℕ := #[
    100411723425, 2013085271533, 712374490541547, 16104774447183, 1606327527721, 10103911371069,
    708613763164775, 708627987685823, 631049700491, 10103911371069, 34441116775017, 5051342249517,
    100411723425, 100411552095, 100411552095, 2013083761171, 712373988708885, 16104762363825,
    1606324786903, 34441116775017, 2414230208182219, 2414275927943887, 17209115639333, 708613763164775,
    2414230208182219, 354255155433191, 2013085271533, 2013083761171, 5051342249517, 354255155433191,
    354262252550585, 5047791672707, 708627987685823, 2414275927943887, 354262252550585, 712374490541547,
    712373988708885, 631049700491, 17209115639333, 5047791672707, 16104774447183, 16104762363825,
    1606327527721, 1606324786903, 3, 7, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    452214200200459304357068800, 18132260157482105117905780736, 200515593134447374778165624832, 18132364049804811128581128192, 452141003454954105236094976, 5687996435716358217324822528,
    199457042483655349646026342400, 199461046330386055682104229888, 5683990391967061413380227072, 5687996435716358217324822528, 19388625084273787514916962304, 5687305768161401057059012608,
    452214200200459304357068800, 452213428598735146969989120, 452213428598735146969989120, 18132246553350624328791621632, 200515451881110525681661378560, 18132350445153164582505676800,
    452140231983271387089338368, 19388625084273787514916962304, 679545391622252279477687025664, 679558260591102996520602959872, 19375741695168968459175329792, 199457042483655349646026342400,
    679545391622252279477687025664, 199427923250374516135891566592, 18132260157482105117905780736, 18132246553350624328791621632, 5687305768161401057059012608, 199427923250374516135891566592,
    199431918572280894019097067520, 5683308174061784475965063168, 199461046330386055682104229888, 679558260591102996520602959872, 199431918572280894019097067520, 200515593134447374778165624832,
    200515451881110525681661378560, 5683990391967061413380227072, 19375741695168968459175329792, 5683308174061784475965063168, 18132364049804811128581128192, 18132350445153164582505676800,
    452141003454954105236094976, 452140231983271387089338368, 950737950171172051122527404032, 4436777100798802905238461218816, 4436777100798802905238461218816, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    36, 40, 49, 43, 40, 43,
    49, 49, 39, 43, 44, 42,
    36, 36, 36, 40, 49, 43,
    40, 44, 51, 51, 43, 49,
    51, 48, 40, 40, 42, 48,
    48, 42, 49, 51, 48, 49,
    49, 39, 43, 42, 43, 43,
    40, 40, 1, 2, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 24584963016668785, 24584961984772880, 26372559009557349, 28141071000372067, 25372349354106879,
    22635226344718293, 27766775860057183, 26766803776618475, 20634246500887152, 12547135531830787, 20872544881415644,
    26339628676085372, 19872553147577094, 17546901993995566
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36547136762649753, 40872545425433891, 49339629184239182, 43872553691613365, 40546903224806310, 43199979122876741,
    49331992815127872, 49332021775107301, 39198962677856650, 43199979122876741, 44969197171692354, 42199803932338537,
    36547136762649753, 36547134301013364, 36547134301013364, 40872544343019389, 49339628167931387, 43872552609163678,
    40546900763186347, 44969197171692354, 51100484673706496, 51100511994650727, 43968238208181475, 49331992815127872,
    51100484673706496, 48331782177088676, 40872545425433891, 40872544343019389, 42199803932338537, 48331782177088676,
    48331811079627849, 42198789508763886, 49332021775107301, 51100511994650727, 48331811079627849, 49339629184239182,
    49339628167931387, 39198962677856650, 43968238208181475, 42198789508763886, 43872553691613365, 43872552609163678,
    40546903224806310, 40546900763186347, 1584962500724866, 2807354922807594, 2807354922807594, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 1871447053 / 500000000000
noncomputable def negativeCeiling : ℝ := 3562302771 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 452214200200459304357068800, coefficient := (-452214200200459304357068800) }, { argument := 18132260157482105117905780736, coefficient := (-18132260157482105117905780736) }, { argument := 200515593134447374778165624832, coefficient := (-200515593134447374778165624832) }, { argument := 18132364049804811128581128192, coefficient := (-18132364049804811128581128192) }, { argument := 452141003454954105236094976, coefficient := (-452141003454954105236094976) }, { argument := 5687996435716358217324822528, coefficient := (-5687996435716358217324822528) }, { argument := 199457042483655349646026342400, coefficient := (-199457042483655349646026342400) }, { argument := 199461046330386055682104229888, coefficient := (-199461046330386055682104229888) }, { argument := 5683990391967061413380227072, coefficient := (-5683990391967061413380227072) }, { argument := 5687996435716358217324822528, coefficient := (-5687996435716358217324822528) }, { argument := 19388625084273787514916962304, coefficient := (-19388625084273787514916962304) }, { argument := 5687305768161401057059012608, coefficient := (-5687305768161401057059012608) }, { argument := 452214200200459304357068800, coefficient := (-452214200200459304357068800) }, { argument := 452213428598735146969989120, coefficient := (-452213428598735146969989120) }, { argument := 452213428598735146969989120, coefficient := (-452213428598735146969989120) }, { argument := 18132246553350624328791621632, coefficient := (-18132246553350624328791621632) }, { argument := 200515451881110525681661378560, coefficient := (-200515451881110525681661378560) }, { argument := 18132350445153164582505676800, coefficient := (-18132350445153164582505676800) }, { argument := 452140231983271387089338368, coefficient := (-452140231983271387089338368) }, { argument := 19388625084273787514916962304, coefficient := (-19388625084273787514916962304) }, { argument := 679545391622252279477687025664, coefficient := (-679545391622252279477687025664) }, { argument := 679558260591102996520602959872, coefficient := (-679558260591102996520602959872) }, { argument := 19375741695168968459175329792, coefficient := (-19375741695168968459175329792) }, { argument := 199457042483655349646026342400, coefficient := (-199457042483655349646026342400) }, { argument := 679545391622252279477687025664, coefficient := (-679545391622252279477687025664) }, { argument := 199427923250374516135891566592, coefficient := (-199427923250374516135891566592) }, { argument := 18132260157482105117905780736, coefficient := (-18132260157482105117905780736) }, { argument := 18132246553350624328791621632, coefficient := (-18132246553350624328791621632) }, { argument := 5687305768161401057059012608, coefficient := (-5687305768161401057059012608) }, { argument := 199427923250374516135891566592, coefficient := (-199427923250374516135891566592) }, { argument := 199431918572280894019097067520, coefficient := (-199431918572280894019097067520) }, { argument := 5683308174061784475965063168, coefficient := (-5683308174061784475965063168) }, { argument := 199461046330386055682104229888, coefficient := (-199461046330386055682104229888) }, { argument := 679558260591102996520602959872, coefficient := (-679558260591102996520602959872) }, { argument := 199431918572280894019097067520, coefficient := (-199431918572280894019097067520) }, { argument := 200515593134447374778165624832, coefficient := (-200515593134447374778165624832) }, { argument := 200515451881110525681661378560, coefficient := (-200515451881110525681661378560) }, { argument := 5683990391967061413380227072, coefficient := (-5683990391967061413380227072) }, { argument := 19375741695168968459175329792, coefficient := (-19375741695168968459175329792) }, { argument := 5683308174061784475965063168, coefficient := (-5683308174061784475965063168) }, { argument := 18132364049804811128581128192, coefficient := (-18132364049804811128581128192) }, { argument := 18132350445153164582505676800, coefficient := (-18132350445153164582505676800) }, { argument := 452141003454954105236094976, coefficient := (-452141003454954105236094976) }, { argument := 452140231983271387089338368, coefficient := (-452140231983271387089338368) }, { argument := 5387515050969974956360988622848, coefficient := 5387515050969974956360988622848 }, { argument := 475369145090779408868491395072, coefficient := 475369145090779408868491395072 }, { argument := 475368805080392642254036008960, coefficient := 475368805080392642254036008960 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 820580151283449649917671243776, coefficient := 820580151283449649917671243776 }, { argument := 2795736037985596063944764555264, coefficient := 2795736037985596063944764555264 }, { argument := 820460911529757191376025419776, coefficient := 820460911529757191376025419776 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 61527854576303093578601594880, coefficient := 61527854576303093578601594880 }, { argument := 2156860714712564290519209869312, coefficient := 2156860714712564290519209869312 }, { argument := 2156902450987539892443608514560, coefficient := 2156902450987539892443608514560 }, { argument := 61486080522395628697041240064, coefficient := 61486080522395628697041240064 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 1808855257598388902654115840, coefficient := 1808855257598388902654115840 }, { argument := 72529013421665458893394804736, coefficient := 72529013421665458893394804736 }, { argument := 802062090031115800919654006784, coefficient := 802062090031115800919654006784 }, { argument := 72529428989915951422173609984, coefficient := 72529428989915951422173609984 }, { argument := 1808562470876450984650866688, coefficient := 1808562470876450984650866688 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7
