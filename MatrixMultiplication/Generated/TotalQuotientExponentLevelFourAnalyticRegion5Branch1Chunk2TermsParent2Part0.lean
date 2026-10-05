import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-54892508946254148312444388245504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    259860441015, 12728148185193, 397762130409, 4061214507, 12755044221, 1746258536347,
    19240488495163, 1744072725405, 50373983897, 12755044221, 463680557057, 57959822491,
    6378095061, 888180638145, 43503715815199, 1359516752287, 13880881901, 463680557057,
    62911095468857, 692162427085249, 62839964798487, 1825177722091, 1746258536347, 62911095468857,
    15727712635251, 54574964219, 259860441015, 888180638145, 32482618065, 32482618065,
    1591021605903, 49720362639, 507652797, 57959822491, 15727712635251, 173039944559303,
    7854964984233, 114073138407, 19240488495163, 692162427085249, 173039944559303, 2405251342685,
    12728148185193, 43503715815199, 1591021605903, 6378095061, 54574964219, 2405251342685,
    436053283905, 12594591107, 1744072725405, 62839964798487, 7854964984233, 436053283905,
    397762130409, 1359516752287, 49720362639, 50373983897, 1825177722091, 114073138407,
    12594591107, 4061214507, 13880881901, 507652797
  ]
def negativeCoefficients : Array ℕ := #[
    146288423165435844419911680, 7165310427993956214129033216, 7165445529168268142844051456, 146320673123174820951883776, 14360903100197449607675904, 491528080849056059078213632,
    5415716051077650133106556928, 490912829765062712025415680, 14179015944231035372306432, 14360903100197449607675904, 522057895995212302351597568, 522055669945855386501251072,
    14362193270026600477360128, 500001248873438918203146240, 24490414791820271253180121088, 24490876556014720462417297408, 500111476455339697182343168, 522057895995212302351597568,
    17707899131938380283948040192, 194826403043811594011718713344, 17687877628152571185145577472, 513741856818372394086301696, 491528080849056059078213632, 17707899131938380283948040192,
    17707830190876661317971738624, 491567577040893104512565248, 146288423165435844419911680, 500001248873438918203146240, 146288706613552141817610240, 146288706613552141817610240,
    7165324311483158939081637888, 7165459412919242596137566208, 146320956633778563179347968, 522055669945855386501251072, 17707830190876661317971738624, 194825657459372069369856131072,
    17687808688000016393944694784, 513739743622748215676239872, 5415716051077650133106556928, 194826403043811594011718713344, 194825657459372069369856131072, 5416144525324275589977210880,
    7165310427993956214129033216, 24490414791820271253180121088, 7165324311483158939081637888, 14362193270026600477360128, 491567577040893104512565248, 5416144525324275589977210880,
    490952351727059775227166720, 14180248954092240678944768, 490912829765062712025415680, 17687877628152571185145577472, 17687808688000016393944694784, 490952351727059775227166720,
    7165445529168268142844051456, 24490876556014720462417297408, 7165459412919242596137566208, 14179015944231035372306432, 513741856818372394086301696, 513739743622748215676239872,
    14180248954092240678944768, 146320673123174820951883776, 500111476455339697182343168, 146320956633778563179347968
  ]
def negativeScales : Array ℕ := #[
    37, 43, 38, 31, 33, 40,
    44, 40, 35, 33, 38, 35,
    32, 39, 45, 40, 33, 38,
    45, 49, 45, 40, 40, 45,
    43, 35, 37, 39, 34, 34,
    40, 35, 28, 35, 43, 47,
    42, 36, 44, 49, 47, 41,
    43, 45, 40, 32, 35, 41,
    38, 33, 40, 45, 42, 38,
    38, 40, 35, 35, 40, 36,
    33, 31, 33, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37918946076542965, 43533087770735336, 38533114972342117, 31919264090301740, 33570348849565312, 40667404306751497,
    44129210661573119, 40665597338424068, 35551959781939089, 33570348849565312, 38754340277243066, 35754334125593495,
    32570478454089269, 39692062165501307, 45306203865743317, 40306231067350097, 33692380179226404, 38754340277243066,
    45838379718897105, 49298103957691523, 45836747607345305, 40731174088430754, 40667404306751497, 45838379718897105,
    43838374102131198, 35667520228248489, 37918946076542965, 39692062165501307, 34918948871903189, 34918948871903189,
    40533090566095261, 35533117767702041, 28919266885661966, 35754334125593495, 43838374102131198, 47298098436607035,
    42836741984295739, 36731168154121359, 44129210661573119, 49298103957691523, 47298098436607035, 41129324798505868,
    43533087770735336, 45306203865743317, 40533090566095261, 32570478454089269, 35667520228248489, 41129324798505868,
    38665713480924545, 33552085233513359, 40665597338424068, 45836747607345305, 42836741984295739, 38665713480924545,
    38533114972342117, 40306231067350097, 35533117767702041, 35551959781939089, 40731174088430754, 36731168154121359,
    33552085233513359, 31919264090301740, 33692380179226404, 28919266885661966
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
noncomputable def negativeCeiling : ℝ := 623056687 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 146288423165435844419911680, coefficient := (-146288423165435844419911680) }, { argument := 7165310427993956214129033216, coefficient := (-7165310427993956214129033216) }, { argument := 7165445529168268142844051456, coefficient := (-7165445529168268142844051456) }, { argument := 146320673123174820951883776, coefficient := (-146320673123174820951883776) }, { argument := 14360903100197449607675904, coefficient := (-14360903100197449607675904) }, { argument := 491528080849056059078213632, coefficient := (-491528080849056059078213632) }, { argument := 5415716051077650133106556928, coefficient := (-5415716051077650133106556928) }, { argument := 490912829765062712025415680, coefficient := (-490912829765062712025415680) }, { argument := 14179015944231035372306432, coefficient := (-14179015944231035372306432) }, { argument := 14360903100197449607675904, coefficient := (-14360903100197449607675904) }, { argument := 522057895995212302351597568, coefficient := (-522057895995212302351597568) }, { argument := 522055669945855386501251072, coefficient := (-522055669945855386501251072) }, { argument := 14362193270026600477360128, coefficient := (-14362193270026600477360128) }, { argument := 500001248873438918203146240, coefficient := (-500001248873438918203146240) }, { argument := 24490414791820271253180121088, coefficient := (-24490414791820271253180121088) }, { argument := 24490876556014720462417297408, coefficient := (-24490876556014720462417297408) }, { argument := 500111476455339697182343168, coefficient := (-500111476455339697182343168) }, { argument := 522057895995212302351597568, coefficient := (-522057895995212302351597568) }, { argument := 17707899131938380283948040192, coefficient := (-17707899131938380283948040192) }, { argument := 194826403043811594011718713344, coefficient := (-194826403043811594011718713344) }, { argument := 17687877628152571185145577472, coefficient := (-17687877628152571185145577472) }, { argument := 513741856818372394086301696, coefficient := (-513741856818372394086301696) }, { argument := 491528080849056059078213632, coefficient := (-491528080849056059078213632) }, { argument := 17707899131938380283948040192, coefficient := (-17707899131938380283948040192) }, { argument := 17707830190876661317971738624, coefficient := (-17707830190876661317971738624) }, { argument := 491567577040893104512565248, coefficient := (-491567577040893104512565248) }, { argument := 146288423165435844419911680, coefficient := (-146288423165435844419911680) }, { argument := 500001248873438918203146240, coefficient := (-500001248873438918203146240) }, { argument := 146288706613552141817610240, coefficient := (-146288706613552141817610240) }, { argument := 146288706613552141817610240, coefficient := (-146288706613552141817610240) }, { argument := 7165324311483158939081637888, coefficient := (-7165324311483158939081637888) }, { argument := 7165459412919242596137566208, coefficient := (-7165459412919242596137566208) }, { argument := 146320956633778563179347968, coefficient := (-146320956633778563179347968) }, { argument := 522055669945855386501251072, coefficient := (-522055669945855386501251072) }, { argument := 17707830190876661317971738624, coefficient := (-17707830190876661317971738624) }, { argument := 194825657459372069369856131072, coefficient := (-194825657459372069369856131072) }, { argument := 17687808688000016393944694784, coefficient := (-17687808688000016393944694784) }, { argument := 513739743622748215676239872, coefficient := (-513739743622748215676239872) }, { argument := 5415716051077650133106556928, coefficient := (-5415716051077650133106556928) }, { argument := 194826403043811594011718713344, coefficient := (-194826403043811594011718713344) }, { argument := 194825657459372069369856131072, coefficient := (-194825657459372069369856131072) }, { argument := 5416144525324275589977210880, coefficient := (-5416144525324275589977210880) }, { argument := 7165310427993956214129033216, coefficient := (-7165310427993956214129033216) }, { argument := 24490414791820271253180121088, coefficient := (-24490414791820271253180121088) }, { argument := 7165324311483158939081637888, coefficient := (-7165324311483158939081637888) }, { argument := 14362193270026600477360128, coefficient := (-14362193270026600477360128) }, { argument := 491567577040893104512565248, coefficient := (-491567577040893104512565248) }, { argument := 5416144525324275589977210880, coefficient := (-5416144525324275589977210880) }, { argument := 490952351727059775227166720, coefficient := (-490952351727059775227166720) }, { argument := 14180248954092240678944768, coefficient := (-14180248954092240678944768) }, { argument := 490912829765062712025415680, coefficient := (-490912829765062712025415680) }, { argument := 17687877628152571185145577472, coefficient := (-17687877628152571185145577472) }, { argument := 17687808688000016393944694784, coefficient := (-17687808688000016393944694784) }, { argument := 490952351727059775227166720, coefficient := (-490952351727059775227166720) }, { argument := 7165445529168268142844051456, coefficient := (-7165445529168268142844051456) }, { argument := 24490876556014720462417297408, coefficient := (-24490876556014720462417297408) }, { argument := 7165459412919242596137566208, coefficient := (-7165459412919242596137566208) }, { argument := 14179015944231035372306432, coefficient := (-14179015944231035372306432) }, { argument := 513741856818372394086301696, coefficient := (-513741856818372394086301696) }, { argument := 513739743622748215676239872, coefficient := (-513739743622748215676239872) }, { argument := 14180248954092240678944768, coefficient := (-14180248954092240678944768) }, { argument := 146320673123174820951883776, coefficient := (-146320673123174820951883776) }, { argument := 500111476455339697182343168, coefficient := (-500111476455339697182343168) }, { argument := 146320956633778563179347968, coefficient := (-146320956633778563179347968) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 54045854745548783019144635219968
def positiveArguments : Array ℕ := #[
    7, 1548309, 5291987, 193539, 680453, 24485391,
    24485297, 680507, 113591, 7707751, 84805769, 7699011,
    223583, 167835, 8220677, 256901, 2623
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 29246730106901670044689760256, 99962808146327540661965815808, 29246786775299464480432324608, 12853393761472394778380337152, 462515959113432260354500460544,
    462514183503634701367900110848, 12854413792632694621746495488, 2145673324622583477875769344, 72797649961409981531021115392, 800967842159171178209317224448, 72715102995289420132685709312,
    2111681730678887771627585536, 1585156757304853808881336320, 77642099062594772812781584384, 77643562996204462402797830144, 1585506212424586162627149824
  ]
def positiveScales : Array ℕ := #[
    2, 20, 22, 17, 19, 24,
    24, 19, 16, 22, 26, 22,
    17, 17, 22, 17, 11
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 20562261991892082, 22335378086900973, 17562264787252007, 19376135990304763, 24545417898414444,
    24545412359863144, 19376250476450203, 16793489006693875, 22877878535059987, 26337659073157997, 22876241701055721,
    17770450972309697, 17356684078540342, 22970825777932037, 17970852979538410, 11357002092264983
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 43173497 / 62500000000
noncomputable def negativeCeiling : ℝ := 36276913 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 29246730106901670044689760256, coefficient := 29246730106901670044689760256 }, { argument := 99962808146327540661965815808, coefficient := 99962808146327540661965815808 }, { argument := 29246786775299464480432324608, coefficient := 29246786775299464480432324608 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 12853393761472394778380337152, coefficient := 12853393761472394778380337152 }, { argument := 462515959113432260354500460544, coefficient := 462515959113432260354500460544 }, { argument := 462514183503634701367900110848, coefficient := 462514183503634701367900110848 }, { argument := 12854413792632694621746495488, coefficient := 12854413792632694621746495488 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2145673324622583477875769344, coefficient := 2145673324622583477875769344 }, { argument := 72797649961409981531021115392, coefficient := 72797649961409981531021115392 }, { argument := 800967842159171178209317224448, coefficient := 800967842159171178209317224448 }, { argument := 72715102995289420132685709312, coefficient := 72715102995289420132685709312 }, { argument := 2111681730678887771627585536, coefficient := 2111681730678887771627585536 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1585156757304853808881336320, coefficient := 1585156757304853808881336320 }, { argument := 77642099062594772812781584384, coefficient := 77642099062594772812781584384 }, { argument := 77643562996204462402797830144, coefficient := 77643562996204462402797830144 }, { argument := 1585506212424586162627149824, coefficient := 1585506212424586162627149824 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk2
