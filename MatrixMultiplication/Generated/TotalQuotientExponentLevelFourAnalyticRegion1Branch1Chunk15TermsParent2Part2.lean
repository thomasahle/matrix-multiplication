import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-169260681214002113959498694524928)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3251301665, 82005, 82005, 58695, 3045, 72633,
    82005, 35145, 925485, 82005, 35145, 82005,
    82005, 3399693, 21087, 925485, 3399693, 72633,
    82005, 21087, 82005, 30717128595, 152355, 126237,
    225657988251, 848835, 61434298431, 3399693, 3399693, 2433327,
    126237, 85278560725, 85278617131, 1625735757, 945, 783,
    11937009221, 5265, 3251473697, 21087, 21087, 15093,
    783, 170146080015, 170146192113, 611, 51987, 58695,
    25155, 662415, 58695, 25155, 58695, 58695,
    2433327, 15093, 662415, 2433327, 51987, 58695,
    15093, 58695, 18847819797, 41475
  ]
def negativeCoefficients : Array ℕ := #[
    7496991215085093486938030080, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 342999644750270940806381568,
    387257663427725255749140480, 331935140080907362070691840, 4370479344398613600597442560, 387257663427725255749140480, 331935140080907362070691840, 387257663427725255749140480,
    387257663427725255749140480, 16054596275246552745485795328, 398322168097088834484830208, 4370479344398613600597442560, 16054596275246552745485795328, 342999644750270940806381568,
    387257663427725255749140480, 398322168097088834484830208, 387257663427725255749140480, 283315504935595227834231029760, 11511618327961676744522465280, 596137377698015402841341952,
    1040663789363588469137451515904, 16034039813946621179870576640, 283315695126138313798135578624, 16054596275246552745485795328, 16054596275246552745485795328, 11491061866661745178907246592,
    596137377698015402841341952, 196638973083546734187197235200, 196639103146927511894818291712, 7497382860214365423642083328, 285608724883956142524334080, 14790451824347728809295872,
    27524869263162252664495931392, 397812152516938912801751040, 7497387893869654537135980544, 398322168097088834484830208, 398322168097088834484830208, 285098709303806220841254912,
    14790451824347728809295872, 196165074573850776695356784640, 196165203814045600113689100288, 23636917625105229623855153152, 245501666344944245724413952, 277179300712033825817886720,
    237582257753171850701045760, 3128166393750096034230435840, 277179300712033825817886720, 237582257753171850701045760, 277179300712033825817886720, 277179300712033825817886720,
    11491061866661745178907246592, 285098709303806220841254912, 3128166393750096034230435840, 11491061866661745178907246592, 245501666344944245724413952, 277179300712033825817886720,
    285098709303806220841254912, 277179300712033825817886720, 86920227035663828544009535488, 3133762398032296563808665600
  ]
def negativeScales : Array ℕ := #[
    31, 16, 16, 15, 11, 16,
    16, 15, 19, 16, 15, 16,
    16, 21, 14, 19, 21, 16,
    16, 14, 16, 34, 17, 16,
    37, 19, 35, 21, 21, 21,
    16, 36, 36, 30, 9, 9,
    33, 12, 31, 14, 14, 13,
    9, 37, 37, 9, 15, 15,
    14, 19, 15, 14, 15, 15,
    21, 13, 19, 21, 15, 15,
    13, 15, 34, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31598370273572334, 16323424255808103, 16323424255808103, 15840949991965165, 11572226512796267, 16148337549250011,
    16323424255808103, 15101031834471655, 19819850082890743, 16323424255808103, 15101031834471655, 16323424255808103,
    16323424255808103, 21696973042997282, 14364066240305450, 19819850082890743, 21696973042997282, 16148337549250011,
    16323424255808103, 14364066240305450, 16323424255808103, 34838324310998441, 17217077321732868, 16945775309620080,
    37715346894456104, 19695124618602028, 35838325279483624, 21696973042997282, 21696973042997282, 21214498777631091,
    16945775309620080, 36311464038325929, 36311464992570804, 30598445638436938, 9884170522387776, 9612868497299083,
    33474722368180485, 12362217815913081, 31598446607045214, 14364066240305450, 14364066240305450, 13881591978134763,
    9612868497299083, 37307982957285090, 37307983907781131, 9255028569818730, 15665863283982959, 15840949991965165,
    14618557569182239, 19337375816628813, 15840949991965165, 14618557569182239, 15840949991965165, 15840949991965165,
    21214498777631091, 13881591978134763, 19337375816628813, 21214498777631091, 15665863283982959, 15840949991965165,
    13881591978134763, 15840949991965165, 34133678599690222, 15339954360730589
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
noncomputable def negativeCeiling : ℝ := 231501049 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7496991215085093486938030080, coefficient := (-7496991215085093486938030080) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 331935140080907362070691840, coefficient := (-331935140080907362070691840) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 283315504935595227834231029760, coefficient := (-283315504935595227834231029760) }, { argument := 11511618327961676744522465280, coefficient := (-11511618327961676744522465280) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 1040663789363588469137451515904, coefficient := (-1040663789363588469137451515904) }, { argument := 16034039813946621179870576640, coefficient := (-16034039813946621179870576640) }, { argument := 283315695126138313798135578624, coefficient := (-283315695126138313798135578624) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 11491061866661745178907246592, coefficient := (-11491061866661745178907246592) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 196638973083546734187197235200, coefficient := (-196638973083546734187197235200) }, { argument := 196639103146927511894818291712, coefficient := (-196639103146927511894818291712) }, { argument := 7497382860214365423642083328, coefficient := (-7497382860214365423642083328) }, { argument := 285608724883956142524334080, coefficient := (-285608724883956142524334080) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 27524869263162252664495931392, coefficient := (-27524869263162252664495931392) }, { argument := 397812152516938912801751040, coefficient := (-397812152516938912801751040) }, { argument := 7497387893869654537135980544, coefficient := (-7497387893869654537135980544) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 285098709303806220841254912, coefficient := (-285098709303806220841254912) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 196165074573850776695356784640, coefficient := (-196165074573850776695356784640) }, { argument := 196165203814045600113689100288, coefficient := (-196165203814045600113689100288) }, { argument := 23636917625105229623855153152, coefficient := (-23636917625105229623855153152) }, { argument := 245501666344944245724413952, coefficient := (-245501666344944245724413952) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 237582257753171850701045760, coefficient := (-237582257753171850701045760) }, { argument := 3128166393750096034230435840, coefficient := (-3128166393750096034230435840) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 237582257753171850701045760, coefficient := (-237582257753171850701045760) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 11491061866661745178907246592, coefficient := (-11491061866661745178907246592) }, { argument := 285098709303806220841254912, coefficient := (-285098709303806220841254912) }, { argument := 3128166393750096034230435840, coefficient := (-3128166393750096034230435840) }, { argument := 11491061866661745178907246592, coefficient := (-11491061866661745178907246592) }, { argument := 245501666344944245724413952, coefficient := (-245501666344944245724413952) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 285098709303806220841254912, coefficient := (-285098709303806220841254912) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 86920227035663828544009535488, coefficient := (-86920227035663828544009535488) }, { argument := 3133762398032296563808665600, coefficient := (-3133762398032296563808665600) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4004893647385656803074733361856512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34365, 138333062349, 231075, 37695664905, 925485, 925485,
    662415, 34365, 26969365795, 26969383645, 30717128595, 152355,
    126237, 225657988251, 848835, 61434298431, 3399693, 3399693,
    2433327, 126237, 2624349981965, 2624351711987, 16361, 167897933785,
    167898044455, 28723, 18183005249159891, 3255, 2697, 8305045451323713,
    18135, 18181849896121125, 72633, 72633, 51987, 2697,
    12522597427441391, 12522597198336273, 1438556905, 85278560725, 85278617131, 16361,
    29, 2697, 3045, 1305, 34365, 3045,
    1305, 3045, 3045, 126237, 783, 34365,
    126237, 2697, 3045, 783, 3045, 1625649741,
    3675, 3045, 11933808197, 20475
  ]
def negativeCoefficients : Array ℕ := #[
    162284124183815357768663040, 318974324760563706926620213248, 4364883340116413071019212800, 86920285398856234751817154560, 4370479344398613600597442560, 4370479344398613600597442560,
    3128166393750096034230435840, 162284124183815357768663040, 124374247162655335029334343680, 124374329481250763958208430080, 283315504935595227834231029760, 11511618327961676744522465280,
    596137377698015402841341952, 1040663789363588469137451515904, 16034039813946621179870576640, 283315695126138313798135578624, 16054596275246552745485795328, 16054596275246552745485795328,
    11491061866661745178907246592, 596137377698015402841341952, 3025669529822039525881114787840, 3025671524401606768827733901312, 316467765355439166837883928576, 193573138439782966034075484160,
    193573266033605880873830318080, 555583621068655900561367891968, 5118060979037016117734587498496, 245940846427851122729287680, 12736222404299433141338112, 18701299799938253321294340685824,
    342560464667364063801507840, 5117735776067336872245854208000, 342999644750270940806381568, 342999644750270940806381568, 245501666344944245724413952, 12736222404299433141338112,
    14099191276983945082109620649984, 14099191019034514068741241700352, 6793392911872692337062581370880, 196638973083546734187197235200, 196639103146927511894818291712, 316467765355439166837883928576,
    17950130569638013986037301248, 12736222404299433141338112, 14379605940338069675704320, 12325376520289774007746560, 162284124183815357768663040, 14379605940338069675704320,
    12325376520289774007746560, 14379605940338069675704320, 14379605940338069675704320, 596137377698015402841341952, 14790451824347728809295872, 162284124183815357768663040,
    596137377698015402841341952, 12736222404299433141338112, 14379605940338069675704320, 14790451824347728809295872, 14379605940338069675704320, 7496986181429804373444132864,
    277675149192735138565324800, 14379605940338069675704320, 27517488204349527409026924544, 386761814947023943001702400
  ]
def negativeScales : Array ℕ := #[
    15, 37, 17, 35, 19, 19,
    19, 15, 34, 34, 34, 17,
    16, 37, 19, 35, 21, 21,
    21, 16, 41, 41, 13, 37,
    37, 14, 54, 11, 11, 52,
    14, 54, 16, 16, 15, 11,
    53, 53, 30, 36, 36, 13,
    4, 11, 11, 10, 15, 11,
    10, 11, 11, 16, 9, 15,
    16, 11, 11, 9, 11, 30,
    11, 11, 33, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15068652338913194, 37009355053368283, 17818001658463628, 35133679568397539, 19819850082890743, 19819850082890743,
    19337375816628813, 15068652338913194, 34650602544804468, 34650603499669264, 34838324310998441, 17217077321732868,
    16945775309620080, 37715346894456104, 19695124618602028, 35838325279483624, 21696973042997282, 21696973042997282,
    21214498777631091, 16945775309620080, 41255097268503757, 41255098219555772, 13997973332350264, 37288793519798431,
    37288794470751215, 14809918820972644, 54013440183062360, 11668441828086828, 11397139806235610, 52882909490213759,
    14146489124857643, 54013348510919385, 16148337549250011, 16148337549250011, 15665863283982959, 11397139806235610,
    53475383354192991, 53475383327798402, 30421975144884495, 36311464038325929, 36311464992570804, 13997973332350264,
    4857980997143165, 11397139806235610, 11572226512796267, 10349834091457248, 15068652338913194, 11572226512796267,
    10349834091457248, 11572226512796267, 11572226512796267, 16945775309620080, 9612868497299083, 15068652338913194,
    16945775309620080, 11397139806235610, 11572226512796267, 9612868497299083, 11572226512796267, 30598369304912807,
    11843528536141147, 11572226512796267, 33474335443728138, 14321575831415734
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
noncomputable def negativeCeiling : ℝ := 437875691 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 318974324760563706926620213248, coefficient := (-318974324760563706926620213248) }, { argument := 4364883340116413071019212800, coefficient := (-4364883340116413071019212800) }, { argument := 86920285398856234751817154560, coefficient := (-86920285398856234751817154560) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 4370479344398613600597442560, coefficient := (-4370479344398613600597442560) }, { argument := 3128166393750096034230435840, coefficient := (-3128166393750096034230435840) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 124374247162655335029334343680, coefficient := (-124374247162655335029334343680) }, { argument := 124374329481250763958208430080, coefficient := (-124374329481250763958208430080) }, { argument := 283315504935595227834231029760, coefficient := (-283315504935595227834231029760) }, { argument := 11511618327961676744522465280, coefficient := (-11511618327961676744522465280) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 1040663789363588469137451515904, coefficient := (-1040663789363588469137451515904) }, { argument := 16034039813946621179870576640, coefficient := (-16034039813946621179870576640) }, { argument := 283315695126138313798135578624, coefficient := (-283315695126138313798135578624) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 16054596275246552745485795328, coefficient := (-16054596275246552745485795328) }, { argument := 11491061866661745178907246592, coefficient := (-11491061866661745178907246592) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 3025669529822039525881114787840, coefficient := (-3025669529822039525881114787840) }, { argument := 3025671524401606768827733901312, coefficient := (-3025671524401606768827733901312) }, { argument := 316467765355439166837883928576, coefficient := (-316467765355439166837883928576) }, { argument := 193573138439782966034075484160, coefficient := (-193573138439782966034075484160) }, { argument := 193573266033605880873830318080, coefficient := (-193573266033605880873830318080) }, { argument := 555583621068655900561367891968, coefficient := (-555583621068655900561367891968) }, { argument := 5118060979037016117734587498496, coefficient := (-5118060979037016117734587498496) }, { argument := 245940846427851122729287680, coefficient := (-245940846427851122729287680) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 18701299799938253321294340685824, coefficient := (-18701299799938253321294340685824) }, { argument := 342560464667364063801507840, coefficient := (-342560464667364063801507840) }, { argument := 5117735776067336872245854208000, coefficient := (-5117735776067336872245854208000) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 342999644750270940806381568, coefficient := (-342999644750270940806381568) }, { argument := 245501666344944245724413952, coefficient := (-245501666344944245724413952) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 14099191276983945082109620649984, coefficient := (-14099191276983945082109620649984) }, { argument := 14099191019034514068741241700352, coefficient := (-14099191019034514068741241700352) }, { argument := 6793392911872692337062581370880, coefficient := (-6793392911872692337062581370880) }, { argument := 196638973083546734187197235200, coefficient := (-196638973083546734187197235200) }, { argument := 196639103146927511894818291712, coefficient := (-196639103146927511894818291712) }, { argument := 316467765355439166837883928576, coefficient := (-316467765355439166837883928576) }, { argument := 17950130569638013986037301248, coefficient := (-17950130569638013986037301248) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 12325376520289774007746560, coefficient := (-12325376520289774007746560) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 162284124183815357768663040, coefficient := (-162284124183815357768663040) }, { argument := 596137377698015402841341952, coefficient := (-596137377698015402841341952) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 7496986181429804373444132864, coefficient := (-7496986181429804373444132864) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 27517488204349527409026924544, coefficient := (-27517488204349527409026924544) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
