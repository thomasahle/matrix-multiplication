import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2

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
def constantNumerator : ℤ := (-1406055743371838103612309897216)
def positiveArguments : Array ℕ := #[
    5, 4194309, 4194299, 12173487, 42747261, 3047029,
    738507, 8203975, 16407959, 738539, 39217, 151941,
    222933, 1215537, 19611
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 79228256961593994986448224256, 79228068066934680200639676416, 114975333976898697407080955904, 403736465161761505854527373312, 115113500975454497486743273472,
    6975001408329226155661983744, 309937412530403980736253132800, 309937582535597364043480825856, 6975303639784129812955660288, 370394092717397752691032064, 11480337372379148214626942976,
    134754729872074062902385967104, 11480422374975839868240789504, 370441316382226449143169024
  ]
def positiveScales : Array ℕ := #[
    2, 22, 21, 23, 25, 21,
    19, 22, 23, 19, 15, 17,
    17, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    164488216053, 637287503769, 935049888297, 5098337778933, 82254593799, 1123097439219,
    99872339411829, 49936197034725, 2246292512475, 1123097439219, 7895059271247, 2248837306827,
    164488216053, 164487823883, 164487823883, 637285984359, 935047658967, 5098325623563,
    82254397689, 7895059271247, 350694689286783, 43836860237613, 3947700373221, 99872339411829,
    350694689286783, 24998103458947, 637287503769, 637285984359, 2248837306827, 24998103458947,
    49996234276967, 2248935068507, 49936197034725, 43836860237613, 49996234276967, 935049888297,
    935047658967, 2246292512475, 3947700373221, 2248935068507, 5098337778933, 5098325623563,
    82254593799, 82254397689, 1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    92598633565391054790721536, 2870087764501941965159399424, 33688722628057544869067882496, 2870109015176447626466820096, 92610439495671977739288576, 632247651095930835019235328,
    28111564409983299128156749824, 28111579794735897163019059200, 632275132634221577345433600, 632247651095930835019235328, 2222261624503498056539308032, 632991428565184186272448512,
    92598633565391054790721536, 92598412793307821554794496, 92598412793307821554794496, 2870080921687632142154072064, 33688642307979486582125101056, 2870102172311472307653574656,
    92610218695441246832295936, 2222261624503498056539308032, 98711779499547987151996059648, 98711833715603209770472833024, 2222357741226057948255485952, 28111564409983299128156749824,
    98711779499547987151996059648, 28145362355670704087973756928, 2870087764501941965159399424, 2870080921687632142154072064, 632991428565184186272448512, 28145362355670704087973756928,
    28145377757459575088248520704, 633018946031785380876910592, 28111579794735897163019059200, 98711833715603209770472833024, 28145377757459575088248520704, 33688722628057544869067882496,
    33688642307979486582125101056, 632275132634221577345433600, 2222357741226057948255485952, 633018946031785380876910592, 2870109015176447626466820096, 2870102172311472307653574656,
    92610439495671977739288576, 92610218695441246832295936, 158456325028528675187087900672, 633825300114114700748351602688, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    37, 39, 39, 42, 36, 40,
    46, 45, 41, 40, 42, 41,
    37, 37, 37, 39, 39, 42,
    36, 42, 48, 45, 41, 46,
    48, 44, 39, 39, 41, 44,
    45, 41, 45, 45, 45, 39,
    39, 41, 41, 41, 42, 42,
    36, 36, 0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 22000001719825483, 21999998278712924, 23537239140154631, 25349328647524448, 21538971800217265,
    19494252070196563, 22967891663951966, 23967892455291020, 19494314581778891, 15259191556827033, 17213151695924778,
    17766250663973315, 20213162377873116, 14259375482558218
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37259193276652518, 39213153415750262, 39766252384138086, 42213164097698600, 36259377202383703, 40030620239120399,
    46505150398850868, 45505151188401384, 41030682946537813, 40030620239120399, 42844087237187755, 41032316431100668,
    37259193276652518, 37259189836999501, 37259189836999501, 39213149976097245, 39766248944485045, 42213160658045583,
    36259373762730686, 42844087237187755, 48317208911857729, 45317209704237452, 41844149634937358, 46505150398850868,
    48317208911857729, 44506883879056977, 39213153415750262, 39213149976097245, 41032316431100668, 44506883879056977,
    45506884668532631, 41032379146720391, 45505151188401384, 45317209704237452, 45506884668532631, 39766252384138086,
    39766248944485045, 41030682946537813, 41844149634937358, 41032379146720391, 42213164097698600, 42213160658045583,
    36259377202383703, 36259373762730686, 0, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 462217607 / 1000000000000
noncomputable def negativeCeiling : ℝ := 214435621 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 92598633565391054790721536, coefficient := (-92598633565391054790721536) }, { argument := 2870087764501941965159399424, coefficient := (-2870087764501941965159399424) }, { argument := 33688722628057544869067882496, coefficient := (-33688722628057544869067882496) }, { argument := 2870109015176447626466820096, coefficient := (-2870109015176447626466820096) }, { argument := 92610439495671977739288576, coefficient := (-92610439495671977739288576) }, { argument := 632247651095930835019235328, coefficient := (-632247651095930835019235328) }, { argument := 28111564409983299128156749824, coefficient := (-28111564409983299128156749824) }, { argument := 28111579794735897163019059200, coefficient := (-28111579794735897163019059200) }, { argument := 632275132634221577345433600, coefficient := (-632275132634221577345433600) }, { argument := 632247651095930835019235328, coefficient := (-632247651095930835019235328) }, { argument := 2222261624503498056539308032, coefficient := (-2222261624503498056539308032) }, { argument := 632991428565184186272448512, coefficient := (-632991428565184186272448512) }, { argument := 92598633565391054790721536, coefficient := (-92598633565391054790721536) }, { argument := 92598412793307821554794496, coefficient := (-92598412793307821554794496) }, { argument := 92598412793307821554794496, coefficient := (-92598412793307821554794496) }, { argument := 2870080921687632142154072064, coefficient := (-2870080921687632142154072064) }, { argument := 33688642307979486582125101056, coefficient := (-33688642307979486582125101056) }, { argument := 2870102172311472307653574656, coefficient := (-2870102172311472307653574656) }, { argument := 92610218695441246832295936, coefficient := (-92610218695441246832295936) }, { argument := 2222261624503498056539308032, coefficient := (-2222261624503498056539308032) }, { argument := 98711779499547987151996059648, coefficient := (-98711779499547987151996059648) }, { argument := 98711833715603209770472833024, coefficient := (-98711833715603209770472833024) }, { argument := 2222357741226057948255485952, coefficient := (-2222357741226057948255485952) }, { argument := 28111564409983299128156749824, coefficient := (-28111564409983299128156749824) }, { argument := 98711779499547987151996059648, coefficient := (-98711779499547987151996059648) }, { argument := 28145362355670704087973756928, coefficient := (-28145362355670704087973756928) }, { argument := 2870087764501941965159399424, coefficient := (-2870087764501941965159399424) }, { argument := 2870080921687632142154072064, coefficient := (-2870080921687632142154072064) }, { argument := 632991428565184186272448512, coefficient := (-632991428565184186272448512) }, { argument := 28145362355670704087973756928, coefficient := (-28145362355670704087973756928) }, { argument := 28145377757459575088248520704, coefficient := (-28145377757459575088248520704) }, { argument := 633018946031785380876910592, coefficient := (-633018946031785380876910592) }, { argument := 28111579794735897163019059200, coefficient := (-28111579794735897163019059200) }, { argument := 98711833715603209770472833024, coefficient := (-98711833715603209770472833024) }, { argument := 28145377757459575088248520704, coefficient := (-28145377757459575088248520704) }, { argument := 33688722628057544869067882496, coefficient := (-33688722628057544869067882496) }, { argument := 33688642307979486582125101056, coefficient := (-33688642307979486582125101056) }, { argument := 632275132634221577345433600, coefficient := (-632275132634221577345433600) }, { argument := 2222357741226057948255485952, coefficient := (-2222357741226057948255485952) }, { argument := 633018946031785380876910592, coefficient := (-633018946031785380876910592) }, { argument := 2870109015176447626466820096, coefficient := (-2870109015176447626466820096) }, { argument := 2870102172311472307653574656, coefficient := (-2870102172311472307653574656) }, { argument := 92610439495671977739288576, coefficient := (-92610439495671977739288576) }, { argument := 92610218695441246832295936, coefficient := (-92610218695441246832295936) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 79228256961593994986448224256, coefficient := 79228256961593994986448224256 }, { argument := 79228068066934680200639676416, coefficient := 79228068066934680200639676416 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 114975333976898697407080955904, coefficient := 114975333976898697407080955904 }, { argument := 403736465161761505854527373312, coefficient := 403736465161761505854527373312 }, { argument := 115113500975454497486743273472, coefficient := 115113500975454497486743273472 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 6975001408329226155661983744, coefficient := 6975001408329226155661983744 }, { argument := 309937412530403980736253132800, coefficient := 309937412530403980736253132800 }, { argument := 309937582535597364043480825856, coefficient := 309937582535597364043480825856 }, { argument := 6975303639784129812955660288, coefficient := 6975303639784129812955660288 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 370394092717397752691032064, coefficient := 370394092717397752691032064 }, { argument := 11480337372379148214626942976, coefficient := 11480337372379148214626942976 }, { argument := 134754729872074062902385967104, coefficient := 134754729872074062902385967104 }, { argument := 11480422374975839868240789504, coefficient := 11480422374975839868240789504 }, { argument := 370441316382226449143169024, coefficient := 370441316382226449143169024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2
