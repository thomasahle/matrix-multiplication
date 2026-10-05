import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

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
def constantNumerator : ℤ := (-873495961665958957387732855291904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3474135, 724129611, 691616949, 724129611, 691616949, 106848923027,
    186713247, 577107195757, 103858377, 16599811, 415095927, 175171807,
    106974563731, 186713247, 16354419, 5963049, 26746464437, 25524880203,
    26746464437, 25524880203, 7794496979009, 22945079661, 41906055219007, 13602343251,
    2076641129, 54373978245, 21990477965, 7804526071873, 22945079661, 2037464985,
    1751756808285, 94348719447971, 8925, 285, 15885, 184365,
    47174362460301, 15885, 8925, 2205, 8145, 2205,
    184365, 8145, 875875667827, 285, 3474135, 53490788995,
    51047805309, 53490788995, 51047805309, 81229376112875, 239469176877, 435801497908117,
    70146324591, 21600098975, 560789076603, 228583671953, 81329451377899, 239469176877,
    21209179971, 94346962034595, 7869060840136797, 7995
  ]
def negativeCoefficients : Array ℕ := #[
    131249109447714678995870023680, 6678916805155926469339250688, 6379040427621415600407969792, 6678916805155926469339250688, 6379040427621415600407969792, 240602384964668004757405696,
    430531435322539714642182144, 2599059751764057090238185472, 478962225107460600058871808, 19138279074309289107521536, 478573020713013916049866752, 403918686582280418716811264,
    240885302678526488150540288, 430531435322539714642182144, 18855361360450805714386944, 450555243732949680350155505664, 246692592172956514482279940096, 235425466308418253407622529024,
    246692592172956514482279940096, 235425466308418253407622529024, 35103293690205389182377918464, 52907751532168164700713910272, 377456189337774708689620434944, 62729736188486841489533435904,
    2394204214975141405370875904, 62688928809685364751068037120, 50706589884863028827709767680, 35148460709090563682895659008, 52907751532168164700713910272, 2349037196089966904853135360,
    986151413629506925017169920, 53113607218595708083426557952, 337176966876892668257894400, 344543858590169314791260160, 9601893322289192220103802880, 6965112772914097118584504320,
    53113610299413074625454669824, 9601893322289192220103802880, 337176966876892668257894400, 333210179031282166278389760, 307709400023786082124431360, 333210179031282166278389760,
    6965112772914097118584504320, 307709400023786082124431360, 986148332812140382989058048, 344543858590169314791260160, 131249109447714678995870023680, 246682723722891088101879316480,
    235416450014918684076813582336, 246682723722891088101879316480, 235416450014918684076813582336, 365824587993481718829940736000, 552178327423988017682033147904, 3925350927172999426482649432064,
    646985648720767918556502294528, 24903218609913813144279449600, 646545785964215126222362902528, 527078061993221374799308128256, 366275286919752808861379067904, 552178327423988017682033147904,
    24452519683642723112841117696, 53112617882817546892754288640, 4429887433424480145400255217664, 302042560244342507867996160
  ]
def negativeScales : Array ℕ := #[
    21, 29, 29, 29, 29, 36,
    27, 39, 26, 23, 28, 27,
    36, 27, 23, 22, 34, 34,
    34, 34, 42, 34, 45, 33,
    30, 35, 34, 42, 34, 30,
    40, 46, 13, 8, 13, 17,
    45, 13, 13, 11, 12, 11,
    17, 12, 39, 8, 21, 35,
    35, 35, 35, 46, 37, 48,
    36, 34, 39, 37, 46, 37,
    34, 46, 52, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21728222385700655, 29431672705594525, 29365397983687291, 29431672705594525, 29365397983687291, 36636781410347234,
    27476249047151779, 39070048363365197, 26630042344759275, 23984663498325964, 28628869535124707, 27384195358385936,
    36638476839079379, 27476249047151779, 23963177184983599, 22507618761153948, 34638629145961435, 34571185138933422,
    34638629145961435, 34571185138933422, 42825593060751041, 34417465764398290, 45252223954865110, 33663136152246243,
    30951604785671560, 35662197334963345, 34356159910512680, 42827448167291860, 34417465764398290, 30924128126693637,
    40671939642029574, 46423068170454198, 13123636453803825, 8154818109052105, 13955377481012500, 17492205273810185,
    45423068254136705, 13955377481012500, 13123636453803825, 11106562940444883, 12991699004141302, 11106562940444883,
    17492205273810185, 12991699004141302, 39671935134925673, 8154818109052105, 21728222385700655, 35638571432640482,
    35571129885730720, 35638571432640482, 35571129885730720, 46207066797252398, 37801049016756406, 48630664483634422,
    36029648462793628, 34330318871929707, 39028667291675565, 37733931397454625, 46208843115512487, 37801049016756406,
    34303969790645342, 46423041297432595, 52805112886681440, 12964882331740830
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
noncomputable def negativeCeiling : ℝ := 417050113 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 131249109447714678995870023680, coefficient := (-131249109447714678995870023680) }, { argument := 6678916805155926469339250688, coefficient := (-6678916805155926469339250688) }, { argument := 6379040427621415600407969792, coefficient := (-6379040427621415600407969792) }, { argument := 6678916805155926469339250688, coefficient := (-6678916805155926469339250688) }, { argument := 6379040427621415600407969792, coefficient := (-6379040427621415600407969792) }, { argument := 240602384964668004757405696, coefficient := (-240602384964668004757405696) }, { argument := 430531435322539714642182144, coefficient := (-430531435322539714642182144) }, { argument := 2599059751764057090238185472, coefficient := (-2599059751764057090238185472) }, { argument := 478962225107460600058871808, coefficient := (-478962225107460600058871808) }, { argument := 19138279074309289107521536, coefficient := (-19138279074309289107521536) }, { argument := 478573020713013916049866752, coefficient := (-478573020713013916049866752) }, { argument := 403918686582280418716811264, coefficient := (-403918686582280418716811264) }, { argument := 240885302678526488150540288, coefficient := (-240885302678526488150540288) }, { argument := 430531435322539714642182144, coefficient := (-430531435322539714642182144) }, { argument := 18855361360450805714386944, coefficient := (-18855361360450805714386944) }, { argument := 450555243732949680350155505664, coefficient := (-450555243732949680350155505664) }, { argument := 246692592172956514482279940096, coefficient := (-246692592172956514482279940096) }, { argument := 235425466308418253407622529024, coefficient := (-235425466308418253407622529024) }, { argument := 246692592172956514482279940096, coefficient := (-246692592172956514482279940096) }, { argument := 235425466308418253407622529024, coefficient := (-235425466308418253407622529024) }, { argument := 35103293690205389182377918464, coefficient := (-35103293690205389182377918464) }, { argument := 52907751532168164700713910272, coefficient := (-52907751532168164700713910272) }, { argument := 377456189337774708689620434944, coefficient := (-377456189337774708689620434944) }, { argument := 62729736188486841489533435904, coefficient := (-62729736188486841489533435904) }, { argument := 2394204214975141405370875904, coefficient := (-2394204214975141405370875904) }, { argument := 62688928809685364751068037120, coefficient := (-62688928809685364751068037120) }, { argument := 50706589884863028827709767680, coefficient := (-50706589884863028827709767680) }, { argument := 35148460709090563682895659008, coefficient := (-35148460709090563682895659008) }, { argument := 52907751532168164700713910272, coefficient := (-52907751532168164700713910272) }, { argument := 2349037196089966904853135360, coefficient := (-2349037196089966904853135360) }, { argument := 986151413629506925017169920, coefficient := (-986151413629506925017169920) }, { argument := 53113607218595708083426557952, coefficient := (-53113607218595708083426557952) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 53113610299413074625454669824, coefficient := (-53113610299413074625454669824) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 986148332812140382989058048, coefficient := (-986148332812140382989058048) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 131249109447714678995870023680, coefficient := (-131249109447714678995870023680) }, { argument := 246682723722891088101879316480, coefficient := (-246682723722891088101879316480) }, { argument := 235416450014918684076813582336, coefficient := (-235416450014918684076813582336) }, { argument := 246682723722891088101879316480, coefficient := (-246682723722891088101879316480) }, { argument := 235416450014918684076813582336, coefficient := (-235416450014918684076813582336) }, { argument := 365824587993481718829940736000, coefficient := (-365824587993481718829940736000) }, { argument := 552178327423988017682033147904, coefficient := (-552178327423988017682033147904) }, { argument := 3925350927172999426482649432064, coefficient := (-3925350927172999426482649432064) }, { argument := 646985648720767918556502294528, coefficient := (-646985648720767918556502294528) }, { argument := 24903218609913813144279449600, coefficient := (-24903218609913813144279449600) }, { argument := 646545785964215126222362902528, coefficient := (-646545785964215126222362902528) }, { argument := 527078061993221374799308128256, coefficient := (-527078061993221374799308128256) }, { argument := 366275286919752808861379067904, coefficient := (-366275286919752808861379067904) }, { argument := 552178327423988017682033147904, coefficient := (-552178327423988017682033147904) }, { argument := 24452519683642723112841117696, coefficient := (-24452519683642723112841117696) }, { argument := 53112617882817546892754288640, coefficient := (-53112617882817546892754288640) }, { argument := 4429887433424480145400255217664, coefficient := (-4429887433424480145400255217664) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }] }

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
def constantNumerator : ℤ := (-322240503846010477513984717094912)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8331, 212295, 176259, 3934530652213107, 212295, 7995,
    7887, 3681, 7887, 176259, 3681, 47173248872589,
    8331, 8925, 7995, 525, 8655, 232395,
    22305, 7995, 232395, 525, 8295, 7695,
    8295, 22305, 7695, 8925, 8655, 421287754255,
    30729614314837, 320228266060615, 30729615171925, 421286269455, 285, 8331,
    8655, 4371, 128103, 171759, 8331, 128103,
    8655, 4281, 7857, 4281, 171759, 7857,
    285, 4371, 15885, 212295, 232395, 128103,
    2415915, 6090219, 212295, 2415915, 232395, 114021,
    219717, 114021, 6090219, 219717
  ]
def negativeCoefficients : Array ℕ := #[
    314736281350296114202411008, 8020278339846490645132738560, 6658876751232966365766746112, 4429887694796185819558359072768, 8020278339846490645132738560, 302042560244342507867996160,
    297962435603143134403362816, 278128496375090624505839616, 297962435603143134403362816, 6658876751232966365766746112, 278128496375090624505839616, 53112356511111872734650433536,
    314736281350296114202411008, 337176966876892668257894400, 302042560244342507867996160, 317343027648840158360371200, 326976655273894234596311040, 8779634870291929595495055360,
    6741272601626075935455313920, 302042560244342507867996160, 8779634870291929595495055360, 317343027648840158360371200, 313376239803229656380866560, 290708880685455359355125760,
    313376239803229656380866560, 6741272601626075935455313920, 290708880685455359355125760, 337176966876892668257894400, 326976655273894234596311040, 237163921634821386335682560,
    34598469894384743237747212288, 360544974926021441263249653760, 34598470859380042593678131200, 237163085766730546371624960, 344543858590169314791260160, 314736281350296114202411008,
    326976655273894234596311040, 330263422345971507665043456, 9679189016880802572961579008, 6488871557849659138073690112, 314736281350296114202411008, 9679189016880802572961579008,
    326976655273894234596311040, 323463214610639218557321216, 296829067647254419552075776, 323463214610639218557321216, 6488871557849659138073690112, 296829067647254419552075776,
    344543858590169314791260160, 330263422345971507665043456, 9601893322289192220103802880, 8020278339846490645132738560, 8779634870291929595495055360, 9679189016880802572961579008,
    182541376343392302663141949440, 230081968631487102429683515392, 8020278339846490645132738560, 182541376343392302663141949440, 8779634870291929595495055360, 8615183179892477070573305856,
    8300673572133358699341152256, 8615183179892477070573305856, 230081968631487102429683515392, 8300673572133358699341152256
  ]
def negativeScales : Array ℕ := #[
    13, 17, 17, 51, 17, 12,
    12, 11, 12, 17, 11, 45,
    13, 13, 12, 9, 13, 17,
    14, 12, 17, 9, 13, 12,
    13, 14, 12, 13, 13, 38,
    44, 48, 44, 38, 8, 13,
    13, 12, 16, 17, 13, 16,
    13, 12, 12, 12, 17, 12,
    8, 12, 13, 17, 17, 16,
    21, 22, 17, 21, 17, 16,
    17, 16, 22, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13024273962540003, 17695710867600679, 17427337399601406, 51805112971803165, 17695710867600679, 12964882331740830,
    12945260936959442, 11845882035984914, 12945260936959442, 17427337399601406, 11845882035984914, 45423034197790242,
    13024273962540003, 13123636453803825, 12964882331740830, 9036173612553486, 13079318104254002, 17826219504887810,
    14445079527660976, 12964882331740830, 17826219504887810, 9036173612553486, 13018026265843226, 12909705616407956,
    13018026265843226, 14445079527660976, 12909705616407956, 13123636453803825, 13079318104254002, 38616015024867283,
    44804694894129988, 48186093986388606, 44804694934368586, 38616009940177898, 8154818109052105, 13024273962540003,
    13079318104254002, 12093747662785669, 16966944750328079, 17390026171239616, 13024273962540003, 16966944750328079,
    13079318104254002, 12063732120196920, 12939762853831857, 12063732120196920, 17390026171239616, 12939762853831857,
    8154818109052105, 12093747662785669, 13955377481012500, 17695710867600679, 17826219504887810, 16966944750328079,
    21204138266025370, 22538062676690401, 17695710867600679, 21204138266025370, 17826219504887810, 16798940034596984,
    17745286973289567, 16798940034596984, 22538062676690401, 17745286973289567
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
noncomputable def negativeCeiling : ℝ := 1647173427 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 4429887694796185819558359072768, coefficient := (-4429887694796185819558359072768) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 53112356511111872734650433536, coefficient := (-53112356511111872734650433536) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 317343027648840158360371200, coefficient := (-317343027648840158360371200) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 302042560244342507867996160, coefficient := (-302042560244342507867996160) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 317343027648840158360371200, coefficient := (-317343027648840158360371200) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 237163921634821386335682560, coefficient := (-237163921634821386335682560) }, { argument := 34598469894384743237747212288, coefficient := (-34598469894384743237747212288) }, { argument := 360544974926021441263249653760, coefficient := (-360544974926021441263249653760) }, { argument := 34598470859380042593678131200, coefficient := (-34598470859380042593678131200) }, { argument := 237163085766730546371624960, coefficient := (-237163085766730546371624960) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 330263422345971507665043456, coefficient := (-330263422345971507665043456) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 330263422345971507665043456, coefficient := (-330263422345971507665043456) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 182541376343392302663141949440, coefficient := (-182541376343392302663141949440) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 8020278339846490645132738560, coefficient := (-8020278339846490645132738560) }, { argument := 182541376343392302663141949440, coefficient := (-182541376343392302663141949440) }, { argument := 8779634870291929595495055360, coefficient := (-8779634870291929595495055360) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
