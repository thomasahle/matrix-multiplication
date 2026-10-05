import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 20, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-676120450011329181875486356144128)
def positiveArguments : Array ℕ := #[
    3885, 35, 273, 273, 273, 273,
    273, 315, 329, 645, 2709, 11739,
    387, 387, 903, 11739, 11739, 387,
    144867, 5805, 2709, 11739, 903, 5805,
    903, 11739, 11739, 387, 459, 8721,
    13311, 137241, 4131, 13311, 4131, 4131,
    353889, 4131, 137241, 353889, 459, 4131,
    4131, 8721, 105, 1869, 105, 3325,
    5677, 105, 5677, 5677, 1869, 105,
    483, 541, 483, 541, 7
  ]
def positiveCoefficients : Array ℕ := #[
    75146828947245349499735900160, 5415987671873538702683668480, 5280587980076700235116576768, 5280587980076700235116576768, 5280587980076700235116576768, 168978815362454407523730456576,
    5280587980076700235116576768, 6092986130857731040519127040, 6363785514451407975653310464, 24952228916845946165935472640, 419197445803011895587715940352, 908261132573192440440051204096,
    29942674700215135399122567168, 479082795203442166385961074688, 34933120483584324632309661696, 908261132573192440440051204096, 908261132573192440440051204096, 479082795203442166385961074688,
    11208541229447199017738214309888, 898280241006454061973677015040, 419197445803011895587715940352, 908261132573192440440051204096, 34933120483584324632309661696, 898280241006454061973677015040,
    34933120483584324632309661696, 908261132573192440440051204096, 908261132573192440440051204096, 29942674700215135399122567168, 284107239015994773089349009408, 337377346331493793043601948672,
    257472185358245263112222539776, 2654627014555701161053604806656, 319620643892994119725517635584, 257472185358245263112222539776, 319620643892994119725517635584, 319620643892994119725517635584,
    13690417580083248128243005390848, 319620643892994119725517635584, 2654627014555701161053604806656, 13690417580083248128243005390848, 284107239015994773089349009408, 319620643892994119725517635584,
    319620643892994119725517635584, 337377346331493793043601948672, 32495926031241232216102010880, 578427483356093933446615793664, 32495926031241232216102010880, 514518828827986176754948505600,
    878473200377887977575291027456, 32495926031241232216102010880, 878473200377887977575291027456, 878473200377887977575291027456, 578427483356093933446615793664, 32495926031241232216102010880,
    37370314935927417048517312512, 41857847578336920545026637824, 37370314935927417048517312512, 41857847578336920545026637824, 277298568799925181577403826176
  ]
def positiveScales : Array ℕ := #[
    11, 5, 8, 8, 8, 8,
    8, 8, 8, 9, 11, 13,
    8, 8, 9, 13, 13, 8,
    17, 12, 11, 13, 9, 12,
    9, 13, 13, 8, 8, 13,
    13, 17, 12, 13, 12, 12,
    18, 12, 17, 18, 8, 12,
    12, 13, 6, 10, 6, 11,
    12, 6, 12, 12, 10, 6,
    8, 9, 8, 9, 2
  ]
def negativeArguments : Array ℕ := #[
    7, 129, 459, 7, 1
  ]
def negativeCoefficients : Array ℕ := #[
    554597137599850363154807652352, 20440865928680199099134339186688, 36365726594047330955436673204224, 4436777100798802905238461218816, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    2, 7, 8, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11923698882884927, 5129283016944966, 8092757140919852, 8092757140919852, 8092757140919852, 8092757140919852,
    8092757140919852, 8299208018387278, 8361943773735241, 9333155350310616, 11403544678202013, 13519021895621918,
    8596189756144093, 8596189756144093, 9818582177422692, 13519021895621918, 13519021895621918, 8596189756144093,
    17144369467823855, 12503080351752909, 11403544678202013, 13519021895621918, 9818582177422692, 12503080351752909,
    9818582177422692, 13519021895621918, 13519021895621918, 8596189756144093, 8842350343321225, 13090277856857393,
    13700331338536850, 17066352017611912, 12012275344856120, 13700331338536850, 12012275344856120, 12012275344856120,
    18432937393328840, 12012275344856120, 17066352017611912, 18432937393328840, 8842350343321225, 12012275344856120,
    12012275344856120, 13090277856857393, 6714245517659862, 10868050853594526, 6714245517659862, 11699138625271509,
    12470913026274870, 6714245517659862, 12470913026274870, 12470913026274870, 10868050853594526, 6714245517659862,
    8915879378478017, 9079484783826815, 8915879378478017, 9079484783826815, 2807354922011143
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 7011227255423255, 8842350344909532, 2807354922807594, 0
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 12088119173 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1152877579 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 75146828947245349499735900160, coefficient := 75146828947245349499735900160 }, { argument := 5415987671873538702683668480, coefficient := 5415987671873538702683668480 }, { argument := 5280587980076700235116576768, coefficient := 5280587980076700235116576768 }, { argument := 5280587980076700235116576768, coefficient := 5280587980076700235116576768 }, { argument := 5280587980076700235116576768, coefficient := 5280587980076700235116576768 }, { argument := 168978815362454407523730456576, coefficient := 168978815362454407523730456576 }, { argument := 5280587980076700235116576768, coefficient := 5280587980076700235116576768 }, { argument := 6092986130857731040519127040, coefficient := 6092986130857731040519127040 }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 24952228916845946165935472640, coefficient := 24952228916845946165935472640 }, { argument := 419197445803011895587715940352, coefficient := 419197445803011895587715940352 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 479082795203442166385961074688, coefficient := 479082795203442166385961074688 }, { argument := 34933120483584324632309661696, coefficient := 34933120483584324632309661696 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 479082795203442166385961074688, coefficient := 479082795203442166385961074688 }, { argument := 11208541229447199017738214309888, coefficient := 11208541229447199017738214309888 }, { argument := 898280241006454061973677015040, coefficient := 898280241006454061973677015040 }, { argument := 419197445803011895587715940352, coefficient := 419197445803011895587715940352 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 34933120483584324632309661696, coefficient := 34933120483584324632309661696 }, { argument := 898280241006454061973677015040, coefficient := 898280241006454061973677015040 }, { argument := 34933120483584324632309661696, coefficient := 34933120483584324632309661696 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 908261132573192440440051204096, coefficient := 908261132573192440440051204096 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 20440865928680199099134339186688, coefficient := (-20440865928680199099134339186688) }, { argument := 284107239015994773089349009408, coefficient := 284107239015994773089349009408 }, { argument := 337377346331493793043601948672, coefficient := 337377346331493793043601948672 }, { argument := 257472185358245263112222539776, coefficient := 257472185358245263112222539776 }, { argument := 2654627014555701161053604806656, coefficient := 2654627014555701161053604806656 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 257472185358245263112222539776, coefficient := 257472185358245263112222539776 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 13690417580083248128243005390848, coefficient := 13690417580083248128243005390848 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 2654627014555701161053604806656, coefficient := 2654627014555701161053604806656 }, { argument := 13690417580083248128243005390848, coefficient := 13690417580083248128243005390848 }, { argument := 284107239015994773089349009408, coefficient := 284107239015994773089349009408 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 319620643892994119725517635584, coefficient := 319620643892994119725517635584 }, { argument := 337377346331493793043601948672, coefficient := 337377346331493793043601948672 }, { argument := 36365726594047330955436673204224, coefficient := (-36365726594047330955436673204224) }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 578427483356093933446615793664, coefficient := 578427483356093933446615793664 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 514518828827986176754948505600, coefficient := 514518828827986176754948505600 }, { argument := 878473200377887977575291027456, coefficient := 878473200377887977575291027456 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 878473200377887977575291027456, coefficient := 878473200377887977575291027456 }, { argument := 878473200377887977575291027456, coefficient := 878473200377887977575291027456 }, { argument := 578427483356093933446615793664, coefficient := 578427483356093933446615793664 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 37370314935927417048517312512, coefficient := 37370314935927417048517312512 }, { argument := 41857847578336920545026637824, coefficient := 41857847578336920545026637824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }] }

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

end TermShard6


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1400575270812734080982110974246912)
def positiveArguments : Array ℕ := #[
    7, 388038837, 1388183319, 97009677, 6344757, 234303435,
    1874427021, 50758515, 15337, 2448509, 97729751, 2448509,
    61341, 49293, 4145011, 2072505, 24647
  ]
def positiveCoefficients : Array ℕ := #[
    277298568799925181577403826176, 3664923195801035102650424623104, 13111020755448681474201955074048, 3664921977430482522281959489536, 479396284780040984913827069952, 17703467012243624492804509532160,
    17703462677111193218470203359232, 479400619912472259248133242880, 2317661911928695956558577664, 370008218707349508241330536448, 3692125604012769537542814957568, 370008218707349508241330536448,
    2317397459405655256426610688, 931118444160373686074867712, 78297044070103963907469082624, 78297025180638032428888227840, 931137333626305164655722496
  ]
def positiveScales : Array ℕ := #[
    2, 28, 30, 26, 22, 27,
    30, 25, 13, 21, 26, 21,
    15, 15, 21, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    7, 129, 459, 7, 1
  ]
def negativeCoefficients : Array ℕ := #[
    554597137599850363154807652352, 20440865928680199099134339186688, 36365726594047330955436673204224, 4436777100798802905238461218816, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    2, 7, 8, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 28531625811365174, 30370550952124826, 26531625331754183, 22597133480181680, 27803802864008473,
    30803802510728812, 25597146526268979, 13904728690754080, 21223472068303875, 26542294480103950, 21223472068303875,
    15904564065315052, 15589095166470589, 21982944498554210, 20982944150498393, 14589124433920475
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 7011227255423255, 8842350344909532, 2807354922807594, 0
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
noncomputable def positiveFloor : ℝ := 10704537623 / 500000000000
noncomputable def negativeCeiling : ℝ := 1152877579 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 3664923195801035102650424623104, coefficient := 3664923195801035102650424623104 }, { argument := 13111020755448681474201955074048, coefficient := 13111020755448681474201955074048 }, { argument := 3664921977430482522281959489536, coefficient := 3664921977430482522281959489536 }, { argument := 20440865928680199099134339186688, coefficient := (-20440865928680199099134339186688) }, { argument := 479396284780040984913827069952, coefficient := 479396284780040984913827069952 }, { argument := 17703467012243624492804509532160, coefficient := 17703467012243624492804509532160 }, { argument := 17703462677111193218470203359232, coefficient := 17703462677111193218470203359232 }, { argument := 479400619912472259248133242880, coefficient := 479400619912472259248133242880 }, { argument := 36365726594047330955436673204224, coefficient := (-36365726594047330955436673204224) }, { argument := 2317661911928695956558577664, coefficient := 2317661911928695956558577664 }, { argument := 370008218707349508241330536448, coefficient := 370008218707349508241330536448 }, { argument := 3692125604012769537542814957568, coefficient := 3692125604012769537542814957568 }, { argument := 370008218707349508241330536448, coefficient := 370008218707349508241330536448 }, { argument := 2317397459405655256426610688, coefficient := 2317397459405655256426610688 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 931118444160373686074867712, coefficient := 931118444160373686074867712 }, { argument := 78297044070103963907469082624, coefficient := 78297044070103963907469082624 }, { argument := 78297025180638032428888227840, coefficient := 78297025180638032428888227840 }, { argument := 931137333626305164655722496, coefficient := 931137333626305164655722496 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
