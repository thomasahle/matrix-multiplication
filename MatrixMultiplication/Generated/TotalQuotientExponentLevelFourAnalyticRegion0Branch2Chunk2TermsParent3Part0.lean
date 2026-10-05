import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 2, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-84031241950499817543618504163328)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    999927147915, 49370823677715, 49364206480587, 1002225553047, 85784321883, 2151484359027,
    900551796535, 1073340330733, 10588559951, 85784321883, 1593390619485, 3187552831705,
    42445836425, 3588111605733, 177127227398189, 177103984047343, 3596034446079, 1593390619485,
    40053275435595, 1066990565005555, 79939044179755, 1574613775945, 2151484359027, 40053275435595,
    80126830435129, 1064218783583, 999927147915, 3588111605733, 62533486377, 62533486377,
    771880156739, 24696858455843, 501415169845, 3187552831705, 80126830435129, 1067269187590633,
    79959245732223, 1574990816323, 900551796535, 1066990565005555, 1067269187590633, 7125658397073,
    49370823677715, 177127227398189, 771880156739, 42445836425, 1064218783583, 7125658397073,
    530927966303, 5239582599, 1073340330733, 79939044179755, 79959245732223, 530927966303,
    49364206480587, 177103984047343, 24696858455843, 10588559951, 1574613775945, 1574990816323,
    5239582599, 1002225553047, 3596034446079, 501415169845
  ]
def negativeCoefficients : Array ℕ := #[
    281454470671727302268682240, 13896651444870733431350231040, 13894788869463239811580035072, 282101414202728654498168832, 24146140004156842860085248, 605589009850465477000691712,
    8111449470605713461708062720, 604236889191357966970781696, 23843317324856878692302848, 24146140004156842860085248, 896999175021036222881464320, 897216359068150459248148480,
    23894881638382378260889600, 1009963630658930678691790848, 49856882206728318132351401984, 49850339785090262675916587008, 1012193711960803274416717824, 896999175021036222881464320,
    22547989540839185357356400640, 300331144435428280456267694080, 22500840598768639691487969280, 886428751824793959755939840, 605589009850465477000691712, 22547989540839185357356400640,
    22553697730626617641611034624, 599101914648135165747920896, 281454470671727302268682240, 1009963630658930678691790848, 281625785945635187947732992, 281625785945635187947732992,
    13904956745057761787616690176, 13903095317369552255127126016, 282271646508981995322736640, 897216359068150459248148480, 22553697730626617641611034624, 300409569721074173276216885248,
    22506526830279089086726668288, 886641006688027013625675776, 8111449470605713461708062720, 300331144435428280456267694080, 300409569721074173276216885248, 8022778125456852156313239552,
    13896651444870733431350231040, 49856882206728318132351401984, 13904956745057761787616690176, 23894881638382378260889600, 599101914648135165747920896, 8022778125456852156313239552,
    597771747800691514196099072, 23596982240433334967599104, 604236889191357966970781696, 22500840598768639691487969280, 22506526830279089086726668288, 597771747800691514196099072,
    13894788869463239811580035072, 49850339785090262675916587008, 13903095317369552255127126016, 23843317324856878692302848, 886428751824793959755939840, 886641006688027013625675776,
    23596982240433334967599104, 282101414202728654498168832, 1012193711960803274416717824, 282271646508981995322736640
  ]
def negativeScales : Array ℕ := #[
    39, 45, 45, 39, 36, 40,
    39, 39, 33, 36, 40, 41,
    35, 41, 47, 47, 41, 40,
    45, 49, 46, 40, 40, 45,
    46, 39, 39, 41, 35, 35,
    39, 44, 38, 41, 46, 49,
    46, 40, 39, 49, 49, 42,
    45, 47, 39, 35, 39, 42,
    38, 32, 39, 46, 46, 38,
    45, 47, 44, 33, 40, 40,
    32, 39, 41, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39863032033694665, 45488723948006075, 45488530569881205, 39866344367746866, 36319994950812384, 40968469504984870,
    39712018301060108, 39965244745075747, 33301787344358877, 36319994950812384, 40535237125356594, 41535586392591569,
    35304903993497599, 41706361903720140, 47331779323760391, 47331589995062277, 41709543979098774, 40535237125356594,
    45186985460226318, 49922468848820586, 46183965556289425, 40518135143858748, 40968469504984870, 45186985460226318,
    46187350642889804, 39952931922190904, 39863032033694665, 41706361903720140, 35863909903984670, 35863909903984670,
    39489585913664146, 44489392770146380, 38867214690373822, 41535586392591569, 46187350642889804, 49922845529746400,
    46184330096519779, 40518480555017658, 39712018301060108, 49922468848820586, 49922845529746400, 42696160461273300,
    45488723948006075, 47331779323760391, 39489585913664146, 35304903993497599, 39952931922190904, 42696160461273300,
    38949725190670947, 32286804740875331, 39965244745075747, 46183965556289425, 46184330096519779, 38949725190670947,
    45488530569881205, 47331589995062277, 44489392770146380, 33301787344358877, 40518135143858748, 40518480555017658,
    32286804740875331, 39866344367746866, 41709543979098774, 38867214690373822
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
noncomputable def negativeCeiling : ℝ := 25469449 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 281454470671727302268682240, coefficient := (-281454470671727302268682240) }, { argument := 13896651444870733431350231040, coefficient := (-13896651444870733431350231040) }, { argument := 13894788869463239811580035072, coefficient := (-13894788869463239811580035072) }, { argument := 282101414202728654498168832, coefficient := (-282101414202728654498168832) }, { argument := 24146140004156842860085248, coefficient := (-24146140004156842860085248) }, { argument := 605589009850465477000691712, coefficient := (-605589009850465477000691712) }, { argument := 8111449470605713461708062720, coefficient := (-8111449470605713461708062720) }, { argument := 604236889191357966970781696, coefficient := (-604236889191357966970781696) }, { argument := 23843317324856878692302848, coefficient := (-23843317324856878692302848) }, { argument := 24146140004156842860085248, coefficient := (-24146140004156842860085248) }, { argument := 896999175021036222881464320, coefficient := (-896999175021036222881464320) }, { argument := 897216359068150459248148480, coefficient := (-897216359068150459248148480) }, { argument := 23894881638382378260889600, coefficient := (-23894881638382378260889600) }, { argument := 1009963630658930678691790848, coefficient := (-1009963630658930678691790848) }, { argument := 49856882206728318132351401984, coefficient := (-49856882206728318132351401984) }, { argument := 49850339785090262675916587008, coefficient := (-49850339785090262675916587008) }, { argument := 1012193711960803274416717824, coefficient := (-1012193711960803274416717824) }, { argument := 896999175021036222881464320, coefficient := (-896999175021036222881464320) }, { argument := 22547989540839185357356400640, coefficient := (-22547989540839185357356400640) }, { argument := 300331144435428280456267694080, coefficient := (-300331144435428280456267694080) }, { argument := 22500840598768639691487969280, coefficient := (-22500840598768639691487969280) }, { argument := 886428751824793959755939840, coefficient := (-886428751824793959755939840) }, { argument := 605589009850465477000691712, coefficient := (-605589009850465477000691712) }, { argument := 22547989540839185357356400640, coefficient := (-22547989540839185357356400640) }, { argument := 22553697730626617641611034624, coefficient := (-22553697730626617641611034624) }, { argument := 599101914648135165747920896, coefficient := (-599101914648135165747920896) }, { argument := 281454470671727302268682240, coefficient := (-281454470671727302268682240) }, { argument := 1009963630658930678691790848, coefficient := (-1009963630658930678691790848) }, { argument := 281625785945635187947732992, coefficient := (-281625785945635187947732992) }, { argument := 281625785945635187947732992, coefficient := (-281625785945635187947732992) }, { argument := 13904956745057761787616690176, coefficient := (-13904956745057761787616690176) }, { argument := 13903095317369552255127126016, coefficient := (-13903095317369552255127126016) }, { argument := 282271646508981995322736640, coefficient := (-282271646508981995322736640) }, { argument := 897216359068150459248148480, coefficient := (-897216359068150459248148480) }, { argument := 22553697730626617641611034624, coefficient := (-22553697730626617641611034624) }, { argument := 300409569721074173276216885248, coefficient := (-300409569721074173276216885248) }, { argument := 22506526830279089086726668288, coefficient := (-22506526830279089086726668288) }, { argument := 886641006688027013625675776, coefficient := (-886641006688027013625675776) }, { argument := 8111449470605713461708062720, coefficient := (-8111449470605713461708062720) }, { argument := 300331144435428280456267694080, coefficient := (-300331144435428280456267694080) }, { argument := 300409569721074173276216885248, coefficient := (-300409569721074173276216885248) }, { argument := 8022778125456852156313239552, coefficient := (-8022778125456852156313239552) }, { argument := 13896651444870733431350231040, coefficient := (-13896651444870733431350231040) }, { argument := 49856882206728318132351401984, coefficient := (-49856882206728318132351401984) }, { argument := 13904956745057761787616690176, coefficient := (-13904956745057761787616690176) }, { argument := 23894881638382378260889600, coefficient := (-23894881638382378260889600) }, { argument := 599101914648135165747920896, coefficient := (-599101914648135165747920896) }, { argument := 8022778125456852156313239552, coefficient := (-8022778125456852156313239552) }, { argument := 597771747800691514196099072, coefficient := (-597771747800691514196099072) }, { argument := 23596982240433334967599104, coefficient := (-23596982240433334967599104) }, { argument := 604236889191357966970781696, coefficient := (-604236889191357966970781696) }, { argument := 22500840598768639691487969280, coefficient := (-22500840598768639691487969280) }, { argument := 22506526830279089086726668288, coefficient := (-22506526830279089086726668288) }, { argument := 597771747800691514196099072, coefficient := (-597771747800691514196099072) }, { argument := 13894788869463239811580035072, coefficient := (-13894788869463239811580035072) }, { argument := 49850339785090262675916587008, coefficient := (-49850339785090262675916587008) }, { argument := 13903095317369552255127126016, coefficient := (-13903095317369552255127126016) }, { argument := 23843317324856878692302848, coefficient := (-23843317324856878692302848) }, { argument := 886428751824793959755939840, coefficient := (-886428751824793959755939840) }, { argument := 886641006688027013625675776, coefficient := (-886641006688027013625675776) }, { argument := 23596982240433334967599104, coefficient := (-23596982240433334967599104) }, { argument := 282101414202728654498168832, coefficient := (-282101414202728654498168832) }, { argument := 1012193711960803274416717824, coefficient := (-1012193711960803274416717824) }, { argument := 282271646508981995322736640, coefficient := (-282271646508981995322736640) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 87748580813687647673420586418176
def positiveArguments : Array ℕ := #[
    11, 1501101, 10771017, 3003997, 1984019, 36757355,
    73533821, 981197, 390113, 9805757, 65314175, 76447,
    96377, 333105, 16444825, 16442651, 333851
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 56709992398416858399394234368, 203458758668876629522752995328, 56743898989763862452028571648, 18738529653953101254463848448, 694326805003763871375498936320,
    694507303295472114954856824832, 18534287303568989098971496448, 3684513111463451806501175296, 92612756391928807283432095744, 1233749883505130038701011763200, 92418752132079556518763036672,
    3641020116156222374083035136, 3146087774552586337816412160, 155316980793313626702636646400, 155296447943846109485247496192, 3153133545345027848475246592
  ]
def positiveScales : Array ℕ := #[
    3, 20, 23, 21, 20, 25,
    26, 19, 18, 23, 25, 16,
    16, 18, 23, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 20517589619765072, 23360651139867738, 21518451941401599, 20919994410730256, 25131529620564439,
    26131904617103257, 19904183297022524, 18573532549505181, 23225197579444737, 25960892794306054, 16222172266746453,
    16556401273463069, 18345617483871068, 23971130318902293, 23970939582527369, 18348844836048204
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3169925001442313, 3169925001442313, 0
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
noncomputable def positiveFloor : ℝ := 111819539 / 100000000000
noncomputable def negativeCeiling : ℝ := 108830739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 56709992398416858399394234368, coefficient := 56709992398416858399394234368 }, { argument := 203458758668876629522752995328, coefficient := 203458758668876629522752995328 }, { argument := 56743898989763862452028571648, coefficient := 56743898989763862452028571648 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 18738529653953101254463848448, coefficient := 18738529653953101254463848448 }, { argument := 694326805003763871375498936320, coefficient := 694326805003763871375498936320 }, { argument := 694507303295472114954856824832, coefficient := 694507303295472114954856824832 }, { argument := 18534287303568989098971496448, coefficient := 18534287303568989098971496448 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3684513111463451806501175296, coefficient := 3684513111463451806501175296 }, { argument := 92612756391928807283432095744, coefficient := 92612756391928807283432095744 }, { argument := 1233749883505130038701011763200, coefficient := 1233749883505130038701011763200 }, { argument := 92418752132079556518763036672, coefficient := 92418752132079556518763036672 }, { argument := 3641020116156222374083035136, coefficient := 3641020116156222374083035136 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3146087774552586337816412160, coefficient := 3146087774552586337816412160 }, { argument := 155316980793313626702636646400, coefficient := 155316980793313626702636646400 }, { argument := 155296447943846109485247496192, coefficient := 155296447943846109485247496192 }, { argument := 3153133545345027848475246592, coefficient := 3153133545345027848475246592 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2
