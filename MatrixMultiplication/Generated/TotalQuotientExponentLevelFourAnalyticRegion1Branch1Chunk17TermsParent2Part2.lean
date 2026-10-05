import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

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
def constantNumerator : ℤ := (-19470665000161561942847537452941312)
def positiveArguments : Array ℕ := #[
    2385, 4187, 159, 1325, 159, 4187,
    8321, 1325, 128419, 8215, 2385, 4187,
    159, 8215, 159, 4187, 4187, 159,
    243, 1107, 27, 11583, 513, 27,
    513, 999, 18873, 999, 11583, 18873,
    243, 999, 999, 1107, 49, 245,
    203, 3647, 1365, 49, 5467, 5467,
    3913, 203, 61, 67, 61, 67,
    543, 35580281473, 35580280191, 62880059793, 459206028643, 125750275963,
    3525670637, 137889477247, 137889475459
  ]
def positiveCoefficients : Array ℕ := #[
    184530437105976997227150704640, 323953434030492950687664570368, 12302029140398466481810046976, 205033819006641108030167449600, 12302029140398466481810046976, 323953434030492950687664570368,
    321903095840426539607362895872, 205033819006641108030167449600, 4967969434530914047570957303808, 317802419460293717446759546880, 184530437105976997227150704640, 323953434030492950687664570368,
    12302029140398466481810046976, 317802419460293717446759546880, 12302029140398466481810046976, 323953434030492950687664570368, 323953434030492950687664570368, 12302029140398466481810046976,
    75204857386586851700121796608, 85649976468057247769583157248, 66848762121410534844552708096, 896191217190159982759784742912, 79382905019175010127906340864, 66848762121410534844552708096,
    79382905019175010127906340864, 77293881202880930914014068736, 2920455295179122741021396434944, 77293881202880930914014068736, 896191217190159982759784742912, 2920455295179122741021396434944,
    75204857386586851700121796608, 77293881202880930914014068736, 77293881202880930914014068736, 85649976468057247769583157248, 7582382740622954183757135872, 151647654812459083675142717440,
    7853182124216631118891319296, 141086478852305683204909563904, 211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144, 211494318586661686339797254144,
    151376855428865406740008534016, 7853182124216631118891319296, 37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504,
    172083568980982141253177460129792, 672092514716652037883803658616832, 672092490500356713728263002783744, 593885373614604802523801485049856, 2168539158395381468835733231894528, 593838888419279597778174107189248,
    16649508845806471628535577444352, 651164645691649358960897044774912, 651164637248058087589971402686464
  ]
def positiveScales : Array ℕ := #[
    11, 12, 7, 10, 7, 12,
    13, 10, 16, 13, 11, 12,
    7, 13, 7, 12, 12, 7,
    7, 10, 4, 13, 9, 4,
    9, 9, 14, 9, 13, 14,
    7, 9, 9, 10, 5, 7,
    7, 11, 10, 5, 12, 12,
    11, 7, 5, 6, 5, 6,
    9, 35, 35, 35, 38, 36,
    31, 37, 37
  ]
def negativeArguments : Array ℕ := #[
    53, 27, 7, 1, 543, 8483,
    21181
  ]
def negativeCoefficients : Array ℕ := #[
    8398185226512019784915658735616, 8556641551540548460102746636288, 1109194275199700726309615304704, 158456325028528675187087900672, 172083568980982141253177460129792, 1344185005217008751612066661400576,
    3356263420429265869137708824133632
  ]
def negativeScales : Array ℕ := #[
    5, 4, 2, 0, 9, 13,
    14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11219773550892873, 12031701202740302, 7312882955284355, 10371776644337923, 7312882955284355, 12031701202740302,
    13022541203454826, 10371776644337923, 16970499143109121, 13004044859837436, 11219773550892873, 12031701202740302,
    7312882955284355, 13004044859837436, 7312882955284355, 12031701202740302, 12031701202740302, 7312882955284355,
    7924812503187618, 10112439506781552, 4754887502147955, 13499721339662996, 9002815015607054, 4754887502147955,
    9002815015607054, 9964340866974576, 14204036147538904, 9964340866974576, 13499721339662996, 14204036147538904,
    7924812503187618, 9964340866974576, 9964340866974576, 10112439506781552, 5614709844114682, 7936637938489789,
    7665335917183229, 11832494484259625, 10414685235807213, 5614709844114682, 12416533660199582, 12416533660199582,
    11934059394410200, 7665335917183229, 5930737337099561, 6066089190457772, 5930737337099561, 6066089190457772,
    9084808387804361, 35050358872578612, 35050358820596587, 35871883538175813, 38740350626173293, 36871770609674228,
    31715250560469792, 37004721408496758, 37004721389789466
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5727920454700926, 4754887502413606, 2807354922807594, 0, 9084808387804362, 13050358846587600,
    14370483083184895
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 2706667662109 / 1000000000000
noncomputable def negativeCeiling : ℝ := 811640726821 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 184530437105976997227150704640, coefficient := 184530437105976997227150704640 }, { argument := 323953434030492950687664570368, coefficient := 323953434030492950687664570368 }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }, { argument := 205033819006641108030167449600, coefficient := 205033819006641108030167449600 }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }, { argument := 323953434030492950687664570368, coefficient := 323953434030492950687664570368 }, { argument := 321903095840426539607362895872, coefficient := 321903095840426539607362895872 }, { argument := 205033819006641108030167449600, coefficient := 205033819006641108030167449600 }, { argument := 4967969434530914047570957303808, coefficient := 4967969434530914047570957303808 }, { argument := 317802419460293717446759546880, coefficient := 317802419460293717446759546880 }, { argument := 184530437105976997227150704640, coefficient := 184530437105976997227150704640 }, { argument := 323953434030492950687664570368, coefficient := 323953434030492950687664570368 }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }, { argument := 317802419460293717446759546880, coefficient := 317802419460293717446759546880 }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }, { argument := 323953434030492950687664570368, coefficient := 323953434030492950687664570368 }, { argument := 323953434030492950687664570368, coefficient := 323953434030492950687664570368 }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }, { argument := 8398185226512019784915658735616, coefficient := (-8398185226512019784915658735616) }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 66848762121410534844552708096, coefficient := 66848762121410534844552708096 }, { argument := 79382905019175010127906340864, coefficient := 79382905019175010127906340864 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 896191217190159982759784742912, coefficient := 896191217190159982759784742912 }, { argument := 2920455295179122741021396434944, coefficient := 2920455295179122741021396434944 }, { argument := 75204857386586851700121796608, coefficient := 75204857386586851700121796608 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 77293881202880930914014068736, coefficient := 77293881202880930914014068736 }, { argument := 85649976468057247769583157248, coefficient := 85649976468057247769583157248 }, { argument := 8556641551540548460102746636288, coefficient := (-8556641551540548460102746636288) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 172083568980982141253177460129792, coefficient := 172083568980982141253177460129792 }, { argument := 172083568980982141253177460129792, coefficient := (-172083568980982141253177460129792) }, { argument := 672092514716652037883803658616832, coefficient := 672092514716652037883803658616832 }, { argument := 672092490500356713728263002783744, coefficient := 672092490500356713728263002783744 }, { argument := 1344185005217008751612066661400576, coefficient := (-1344185005217008751612066661400576) }, { argument := 593885373614604802523801485049856, coefficient := 593885373614604802523801485049856 }, { argument := 2168539158395381468835733231894528, coefficient := 2168539158395381468835733231894528 }, { argument := 593838888419279597778174107189248, coefficient := 593838888419279597778174107189248 }, { argument := 3356263420429265869137708824133632, coefficient := (-3356263420429265869137708824133632) }, { argument := 16649508845806471628535577444352, coefficient := 16649508845806471628535577444352 }, { argument := 651164645691649358960897044774912, coefficient := 651164645691649358960897044774912 }, { argument := 651164637248058087589971402686464, coefficient := 651164637248058087589971402686464 }] }

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
def constantNumerator : ℤ := (-132908767096759998241415782041911296)
def positiveArguments : Array ℕ := #[
    3525683985, 8114051, 715099661, 28874915047, 2860403929, 8114051
  ]
def positiveCoefficients : Array ℕ := #[
    16649571879954284972559889858560, 76635044965389855231670484992, 13507850684071382398017128628224, 136357931013661186320502160883712, 13507875641778244364092083011584, 76635044965389855231670484992
  ]
def positiveScales : Array ℕ := #[
    31, 22, 29, 34, 31, 22
  ]
def negativeArguments : Array ℕ := #[
    8429, 129
  ]
def negativeCoefficients : Array ℕ := #[
    1335628363665468203151963914764288, 163526927429441592793074713493504
  ]
def negativeScales : Array ℕ := #[
    13, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    31715256022425525, 22951990939136851, 29413569078487701, 34749097650836188, 31413571744072886, 22951990939136851
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13041145767476330, 7011227255423255
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 73324041779 / 1000000000000
noncomputable def negativeCeiling : ℝ := 111731914713 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16649571879954284972559889858560, coefficient := 16649571879954284972559889858560 }, { argument := 1335628363665468203151963914764288, coefficient := (-1335628363665468203151963914764288) }, { argument := 76635044965389855231670484992, coefficient := 76635044965389855231670484992 }, { argument := 13507850684071382398017128628224, coefficient := 13507850684071382398017128628224 }, { argument := 136357931013661186320502160883712, coefficient := 136357931013661186320502160883712 }, { argument := 13507875641778244364092083011584, coefficient := 13507875641778244364092083011584 }, { argument := 76635044965389855231670484992, coefficient := 76635044965389855231670484992 }, { argument := 163526927429441592793074713493504, coefficient := (-163526927429441592793074713493504) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
