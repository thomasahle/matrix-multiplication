/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20Root0DualData
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Canonical q20 integer-dual partitions for all six roots

This is the six-root arithmetic instance of `eq:partition` in
`better_bound/paper.tex:2274-2307`, with logarithmic potentials from positive integer factors
as in `prop:dual`. The support is exactly the committed `shapes 16`, the 153 ordered triples
of total sixteen for eight CW letters [coppersmith1990matrix]. The root argument is `Fin 6`;
its value is the literal canonical root number 0,...,5, without a shifted indexing convention.

The factors are copied exactly from the six `root_rows` in
`better_bound/legal_hybrid/standard_integer_dual_witness.json`, SHA-256
`6b45b2c1c24ce9c1d08881d48708919c37ea7d90989762e9b6bb7b5aebb52b6a`.
The witness names `better_bound/legal_hybrid/candidate_b32.npz`, SHA-256
`0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`.
The concrete consumer is `legal_hybrid/check_directed.py:684-688`, calling
`export_simplified_exponent_scalar.py:474-507`. No floating-point generation is trusted.

Root zero reuses the imported factors and checked partition theorem unchanged. Roots one,
four and five use seventeen fixed-X subtotals each, with at most seventeen integer products
per check. Roots two and three share the constant-factor list-sum proof. Off the coordinate
alphabet 0,...,16, the nonconstant rows default to one and the constant rows remain constant;
these positive defaults never change the sum over `shapes 16`.

This is a concrete arithmetic ingredient for blueprint S11, currently a theorem card, not a
proof of its complete semantic reconstruction. It proves no root marginal matching, full dual
bound, entropy recurrence, tensor extraction, numerical margin or exponent endpoint.

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix multiplication via
  arithmetic progressions*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `eq:partition` and `prop:dual`.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20RootDualData

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm

/-- Root-1 X-coordinate integer factors, with positive default one off the root alphabet. -/
def root1XFactor : ℕ → ℕ
  | 0 => 12485545879
  | 1 => 83936724573
  | 2 => 400573997492
  | 3 => 1327627793227
  | 4 => 3264463466054
  | 5 => 6427437135202
  | 6 => 10150907813922
  | 7 => 12145124609229
  | 8 => 10185730658131
  | 9 => 5219209638099
  | 10 => 2121289205494
  | 11 => 851272707483
  | 12 => 560617144669
  | 13 => 415994236719
  | 14 => 4294967296
  | 15 => 5787582322
  | 16 => 42962640130
  | _ => 1

/-- Every value of the root-1 X factor is strictly positive. -/
theorem root1XFactor_pos (i : ℕ) : 0 < root1XFactor i := by
  unfold root1XFactor
  split <;> decide

/-- Root-1 Y-coordinate integer factors, with positive default one off the root alphabet. -/
def root1YFactor : ℕ → ℕ
  | 0 => 11409943197
  | 1 => 73607509450
  | 2 => 438819015289
  | 3 => 1336240248766
  | 4 => 3058694144500
  | 5 => 6309118947617
  | 6 => 9922658405891
  | 7 => 11143117012652
  | 8 => 8718343023580
  | 9 => 4447298793863
  | 10 => 1667951998436
  | 11 => 567724022197
  | 12 => 253487176777
  | 13 => 244459966498
  | 14 => 4294967296
  | 15 => 5533027151
  | 16 => 41123134346
  | _ => 1

/-- Every value of the root-1 Y factor is strictly positive. -/
theorem root1YFactor_pos (i : ℕ) : 0 < root1YFactor i := by
  unfold root1YFactor
  split <;> decide

/-- Root-1 Z-coordinate integer factors, with positive default one off the root alphabet. -/
def root1ZFactor : ℕ → ℕ
  | 0 => 12626675145
  | 1 => 86516405160
  | 2 => 382547782297
  | 3 => 1181403384016
  | 4 => 3069476096793
  | 5 => 6199701352476
  | 6 => 9961789097855
  | 7 => 11492148520174
  | 8 => 10228922415587
  | 9 => 4938320825591
  | 10 => 1919844236954
  | 11 => 635885135534
  | 12 => 410621624800
  | 13 => 277479206860
  | 14 => 4294967296
  | 15 => 5495392978
  | 16 => 42173304329
  | _ => 1

/-- Every value of the root-1 Z factor is strictly positive. -/
theorem root1ZFactor_pos (i : ℕ) : 0 < root1ZFactor i := by
  unfold root1ZFactor
  split <;> decide

/-- Root-4 X-coordinate integer factors, with positive default one off the root alphabet. -/
def root4XFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 28793484633
  | 2 => 3911264142634
  | 3 => 11262844728930
  | 4 => 20319960486858
  | 5 => 27354717397580
  | 6 => 27279259246371
  | 7 => 22055841099553
  | 8 => 11998357750474
  | 9 => 7632034382620
  | 10 => 86041105354
  | 11 => 83235128111
  | 12 => 112862825861
  | 13 => 151748878169
  | 14 => 132397112410
  | 15 => 430122210472
  | 16 => 1961323743760
  | _ => 1

/-- Every value of the root-4 X factor is strictly positive. -/
theorem root4XFactor_pos (i : ℕ) : 0 < root4XFactor i := by
  unfold root4XFactor
  split <;> decide

/-- Root-4 Y-coordinate integer factors, with positive default one off the root alphabet. -/
def root4YFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 27257223877
  | 2 => 4111227010115
  | 3 => 11239722798267
  | 4 => 18920679698691
  | 5 => 25966900528420
  | 6 => 26237384827404
  | 7 => 19957523197525
  | 8 => 10593198793859
  | 9 => 7502804425144
  | 10 => 79815317214
  | 11 => 79673502649
  | 12 => 107020596323
  | 13 => 135918732196
  | 14 => 123214434619
  | 15 => 415763531894
  | 16 => 1795993244079
  | _ => 1

/-- Every value of the root-4 Y factor is strictly positive. -/
theorem root4YFactor_pos (i : ℕ) : 0 < root4YFactor i := by
  unfold root4YFactor
  split <;> decide

/-- Root-4 Z-coordinate integer factors, with positive default one off the root alphabet. -/
def root4ZFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 28926227363
  | 2 => 4128338462186
  | 3 => 11555422931972
  | 4 => 20680443161514
  | 5 => 27002450169467
  | 6 => 29226968899993
  | 7 => 24295479323482
  | 8 => 12971426713691
  | 9 => 7873233942046
  | 10 => 86415720946
  | 11 => 82543686156
  | 12 => 112694235017
  | 13 => 150475226652
  | 14 => 128412008329
  | 15 => 400684009654
  | 16 => 1906983648412
  | _ => 1

/-- Every value of the root-4 Z factor is strictly positive. -/
theorem root4ZFactor_pos (i : ℕ) : 0 < root4ZFactor i := by
  unfold root4ZFactor
  split <;> decide

/-- Root-5 X-coordinate integer factors, with positive default one off the root alphabet. -/
def root5XFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 26386339914
  | 2 => 1972318048318
  | 3 => 6704110019788
  | 4 => 17205781235131
  | 5 => 29895922210669
  | 6 => 33027743357208
  | 7 => 37126220126645
  | 8 => 42991447235697
  | 9 => 323798006403
  | 10 => 229949400113
  | 11 => 282908349922
  | 12 => 348630117193
  | 13 => 250614104944
  | 14 => 210352244745
  | 15 => 603730926273
  | 16 => 3304915291592
  | _ => 1

/-- Every value of the root-5 X factor is strictly positive. -/
theorem root5XFactor_pos (i : ℕ) : 0 < root5XFactor i := by
  unfold root5XFactor
  split <;> decide

/-- Root-5 Y-coordinate integer factors, with positive default one off the root alphabet. -/
def root5YFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 25631286688
  | 2 => 1935528287937
  | 3 => 6421977142979
  | 4 => 16467289361294
  | 5 => 28347788639469
  | 6 => 31523220962479
  | 7 => 35211822799685
  | 8 => 41072597658009
  | 9 => 297705999983
  | 10 => 212097913266
  | 11 => 263526488503
  | 12 => 326025464859
  | 13 => 236355105282
  | 14 => 203652441246
  | 15 => 608322662202
  | 16 => 3138550108211
  | _ => 1

/-- Every value of the root-5 Y factor is strictly positive. -/
theorem root5YFactor_pos (i : ℕ) : 0 < root5YFactor i := by
  unfold root5YFactor
  split <;> decide

/-- Root-5 Z-coordinate integer factors, with positive default one off the root alphabet. -/
def root5ZFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 26364607195
  | 2 => 2072694034668
  | 3 => 6751682095150
  | 4 => 17234553328006
  | 5 => 28881203156378
  | 6 => 35127075139827
  | 7 => 36774409747712
  | 8 => 43718790339507
  | 9 => 322397941817
  | 10 => 227254315935
  | 11 => 274799605720
  | 12 => 340278200600
  | 13 => 252979268011
  | 14 => 208320189568
  | 15 => 582925774625
  | 16 => 3247473378741
  | _ => 1

/-- Every value of the root-5 Z factor is strictly positive. -/
theorem root5ZFactor_pos (i : ℕ) : 0 < root5ZFactor i := by
  unfold root5ZFactor
  split <;> decide

/-- Canonical X factor at the literal root number; roots two and three are constant. -/
def xFactor (root : Fin 6) : ℕ → ℕ :=
  match root.val with
  | 0 => LegalHybridQ20Root0DualData.xFactor
  | 1 => root1XFactor
  | 2 => fun _ ↦ 4294967296
  | 3 => fun _ ↦ 4294967296
  | 4 => root4XFactor
  | _ => root5XFactor

/-- The canonical X factors satisfy positivity at every root and coordinate. -/
theorem xFactor_pos (root : Fin 6) (i : ℕ) : 0 < xFactor root i := by
  fin_cases root
  · exact LegalHybridQ20Root0DualData.xFactor_pos i
  · exact root1XFactor_pos i
  · change 0 < (4294967296 : ℕ)
    decide
  · change 0 < (4294967296 : ℕ)
    decide
  · exact root4XFactor_pos i
  · exact root5XFactor_pos i

/-- Canonical Y factor at the literal root number; roots two and three are constant. -/
def yFactor (root : Fin 6) : ℕ → ℕ :=
  match root.val with
  | 0 => LegalHybridQ20Root0DualData.yFactor
  | 1 => root1YFactor
  | 2 => fun _ ↦ 4294967296
  | 3 => fun _ ↦ 4294967296
  | 4 => root4YFactor
  | _ => root5YFactor

/-- The canonical Y factors satisfy positivity at every root and coordinate. -/
theorem yFactor_pos (root : Fin 6) (i : ℕ) : 0 < yFactor root i := by
  fin_cases root
  · exact LegalHybridQ20Root0DualData.yFactor_pos i
  · exact root1YFactor_pos i
  · change 0 < (4294967296 : ℕ)
    decide
  · change 0 < (4294967296 : ℕ)
    decide
  · exact root4YFactor_pos i
  · exact root5YFactor_pos i

/-- Canonical Z factor at the literal root number; roots two and three are constant. -/
def zFactor (root : Fin 6) : ℕ → ℕ :=
  match root.val with
  | 0 => LegalHybridQ20Root0DualData.zFactor
  | 1 => root1ZFactor
  | 2 => fun _ ↦ 4294967296
  | 3 => fun _ ↦ 4294967296
  | 4 => root4ZFactor
  | _ => root5ZFactor

/-- The canonical Z factors satisfy positivity at every root and coordinate. -/
theorem zFactor_pos (root : Fin 6) (i : ℕ) : 0 < zFactor root i := by
  fin_cases root
  · exact LegalHybridQ20Root0DualData.zFactor_pos i
  · exact root1ZFactor_pos i
  · change 0 < (4294967296 : ℕ)
    decide
  · change 0 < (4294967296 : ℕ)
    decide
  · exact root4ZFactor_pos i
  · exact root5ZFactor_pos i

/-- The fixed-X part of the committed shape partition, with at most seventeen products. -/
def fixedXSubtotal (root : Fin 6) (x : ℕ) : ℕ :=
  ((List.range (16 - x + 1)).map fun y ↦
    xFactor root x * yFactor root y * zFactor root (16 - x - y)).sum

/-- Exact fixed-X subtotal for canonical root 1 at X = 0. -/
theorem fixedXSubtotal_root1_0 :
    fixedXSubtotal 1 0 = 3011675144901748937522996998882186094 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 1. -/
theorem fixedXSubtotal_root1_1 :
    fixedXSubtotal 1 1 = 28092285420116183321684693201498113272 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 2. -/
theorem fixedXSubtotal_root1_2 :
    fixedXSubtotal 1 2 = 155409223551555067271667120000860228500 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 3. -/
theorem fixedXSubtotal_root1_3 :
    fixedXSubtotal 1 3 = 501140822113121382249510021043825130099 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 4. -/
theorem fixedXSubtotal_root1_4 :
    fixedXSubtotal 1 4 = 1018257425330964607281754071371990554608 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 5. -/
theorem fixedXSubtotal_root1_5 :
    fixedXSubtotal 1 5 = 1425982750670603472956112358349472445484 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 6. -/
theorem fixedXSubtotal_root1_6 :
    fixedXSubtotal 1 6 = 1392480479375634152608514036289478936164 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 7. -/
theorem fixedXSubtotal_root1_7 :
    fixedXSubtotal 1 7 = 902238711745343088446093747302745959161 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 8. -/
theorem fixedXSubtotal_root1_8 :
    fixedXSubtotal 1 8 = 359867699886146509604354602486594480039 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 9. -/
theorem fixedXSubtotal_root1_9 :
    fixedXSubtotal 1 9 = 76788957505339710001896646262637160521 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 10. -/
theorem fixedXSubtotal_root1_10 :
    fixedXSubtotal 1 10 = 11320939486407390674910877824727461602 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 11. -/
theorem fixedXSubtotal_root1_11 :
    fixedXSubtotal 1 11 = 1422104825728181467337980339448238879 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 12. -/
theorem fixedXSubtotal_root1_12 :
    fixedXSubtotal 1 12 = 248958743804702717380615375981724066 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 13. -/
theorem fixedXSubtotal_root1_13 :
    fixedXSubtotal 1 13 = 40133231293183109975514517908714528 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 14. -/
theorem fixedXSubtotal_root1_14 :
    fixedXSubtotal 1 14 = 69896000262911873174153717612544 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 15. -/
theorem fixedXSubtotal_root1_15 :
    fixedXSubtotal 1 15 = 11092279903806369347535862139940 := by
  decide

/-- Exact fixed-X subtotal for canonical root 1 at X = 16. -/
theorem fixedXSubtotal_root1_16 :
    fixedXSubtotal 1 16 = 6189612362119224444427037613450 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 0. -/
theorem fixedXSubtotal_root4_0 :
    fixedXSubtotal 4 0 = 2123436484986488791499239386446299136 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 1. -/
theorem fixedXSubtotal_root4_1 :
    fixedXSubtotal 4 1 = 27451822363024074485046999366763559934 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 2. -/
theorem fixedXSubtotal_root4_2 :
    fixedXSubtotal 4 2 = 6054272815739131671690062746852893956216 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 3. -/
theorem fixedXSubtotal_root4_3 :
    fixedXSubtotal 4 3 = 24218667783874836065749404890495022737340 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 4. -/
theorem fixedXSubtotal_root4_4 :
    fixedXSubtotal 4 4 = 52364561124083429949297744428672601820866 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 5. -/
theorem fixedXSubtotal_root4_5 :
    fixedXSubtotal 4 5 = 73074766698686323168448245105041159193540 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 6. -/
theorem fixedXSubtotal_root4_6 :
    fixedXSubtotal 4 6 = 65414299943359379968267592059727576456586 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 7. -/
theorem fixedXSubtotal_root4_7 :
    fixedXSubtotal 4 7 = 41081220562008122675560407090905418538620 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 8. -/
theorem fixedXSubtotal_root4_8 :
    fixedXSubtotal 4 8 = 14693943058815296642070182657485843675694 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 9. -/
theorem fixedXSubtotal_root4_9 :
    fixedXSubtotal 4 9 = 5121384485287662511525332395861267886000 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 10. -/
theorem fixedXSubtotal_root4_10 :
    fixedXSubtotal 4 10 = 25359589392341643244236292142117481614 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 11. -/
theorem fixedXSubtotal_root4_11 :
    fixedXSubtotal 4 11 = 7927883244572396778023289695508420155 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 12. -/
theorem fixedXSubtotal_root4_12 :
    fixedXSubtotal 4 12 = 2007007313701667214278537975624711535 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 13. -/
theorem fixedXSubtotal_root4_13 :
    fixedXSubtotal 4 13 = 49979060316631909557042567745056259 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 14. -/
theorem fixedXSubtotal_root4_14 :
    fixedXSubtotal 4 14 = 4789745282222630518230951594987270 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 15. -/
theorem fixedXSubtotal_root4_15 :
    fixedXSubtotal 4 15 = 103791106961074607318218183802880 := by
  decide

/-- Exact fixed-X subtotal for canonical root 4 at X = 16. -/
theorem fixedXSubtotal_root4_16 :
    fixedXSubtotal 4 16 = 36180037146830611166364077916160 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 0. -/
theorem fixedXSubtotal_root5_0 :
    fixedXSubtotal 5 0 = 8002752726227187409086520373484191744 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 1. -/
theorem fixedXSubtotal_root5_1 :
    fixedXSubtotal 5 1 = 81731054808563538804110792537258240478 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 2. -/
theorem fixedXSubtotal_root5_2 :
    fixedXSubtotal 5 2 = 8176913521678092502310133928970719509574 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 3. -/
theorem fixedXSubtotal_root5_3 :
    fixedXSubtotal 5 3 = 32421894331067139794343173044872340665608 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 4. -/
theorem fixedXSubtotal_root5_4 :
    fixedXSubtotal 5 4 = 79138441108723854269254104241733613472928 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 5. -/
theorem fixedXSubtotal_root5_5 :
    fixedXSubtotal 5 5 = 109956105357362483196608806838709951782593 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 6. -/
theorem fixedXSubtotal_root5_6 :
    fixedXSubtotal 5 6 = 85347847739754887509813512814208594939520 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 7. -/
theorem fixedXSubtotal_root5_7 :
    fixedXSubtotal 5 7 = 57506435358458501983850856448258777996980 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 8. -/
theorem fixedXSubtotal_root5_8 :
    fixedXSubtotal 5 8 = 34231449646863114595618502332382977453158 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 9. -/
theorem fixedXSubtotal_root5_9 :
    fixedXSubtotal 5 9 = 109624766930899631390412198192225124035 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 10. -/
theorem fixedXSubtotal_root5_10 :
    fixedXSubtotal 5 10 = 25897514846084861822007924332303703367 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 11. -/
theorem fixedXSubtotal_root5_11 :
    fixedXSubtotal 5 11 = 7780137893770022111437844646066776024 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 12. -/
theorem fixedXSubtotal_root5_12 :
    fixedXSubtotal 5 12 = 1568442779051487760942986096391212453 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 13. -/
theorem fixedXSubtotal_root5_13 :
    fixedXSubtotal 5 13 = 40282631994583955329058454013727952 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 14. -/
theorem fixedXSubtotal_root5_14 :
    fixedXSubtotal 5 14 = 3763399935697188636956109602008800 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 15. -/
theorem fixedXSubtotal_root5_15 :
    fixedXSubtotal 5 15 = 134825591183965614927815286718464 := by
  decide

/-- Exact fixed-X subtotal for canonical root 5 at X = 16. -/
theorem fixedXSubtotal_root5_16 :
    fixedXSubtotal 5 16 = 60964926569286800720108214812672 := by
  decide

/-- The canonical integer partition on the committed root alphabet, at a literal root number. -/
def partitionNumerator (root : Fin 6) : ℕ :=
  integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
    (xFactor root) (yFactor root) (zFactor root)

/-- The exact six canonical partition integers, indexed by root number zero through five. -/
def expectedPartition (root : Fin 6) : ℕ :=
  match root.val with
  | 0 => 83307604927592561572213746647943930712389
  | 1 => 5876302254208851909486182247482668698951
  | 2 => 12121908864682443651812224401408
  | 3 => 12121908864682443651812224401408
  | 4 => 282088041119429551885567349491709846499805
  | _ => 407013735975715118615493469577801822336350

/-- The existing list-sum identity groups the committed shape partition by its X coordinate. -/
theorem partitionNumerator_eq_sum_fixedXSubtotal (root : Fin 6) :
    partitionNumerator root = ((List.range 17).map (fixedXSubtotal root)).sum := by
  unfold partitionNumerator integerPartitionNumeratorOn shapes
  generalize List.range 17 = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map]
    change fixedXSubtotal root x + _ = fixedXSubtotal root x + _
    exact congrArg (fun value ↦ fixedXSubtotal root x + value) ih

/-- Roots two and three share one constant-factor partition on the 153 committed root shapes. -/
theorem constantPartition_eq :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (fun _ ↦ 4294967296) (fun _ ↦ 4294967296) (fun _ ↦ 4294967296) =
      12121908864682443651812224401408 := by
  have hLength : (shapes 16).length = 153 := by
    unfold shapes
    rw [List.length_flatMap]
    simp only [List.length_map, List.length_range]
    decide
  unfold integerPartitionNumeratorOn
  rw [List.map_const', List.sum_const_nat, hLength]

/-- All six literal root partitions agree with the canonical exact integer values. -/
theorem partitionNumerator_eq (root : Fin 6) :
    partitionNumerator root = expectedPartition root := by
  have hRange : List.range 17 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by decide
  fin_cases root
  · exact LegalHybridQ20Root0DualData.partitionNumerator_eq
  · change partitionNumerator (1 : Fin 6) = 5876302254208851909486182247482668698951
    rw [partitionNumerator_eq_sum_fixedXSubtotal]
    rw [hRange]
    norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fixedXSubtotal_root1_0, fixedXSubtotal_root1_1,
      fixedXSubtotal_root1_2, fixedXSubtotal_root1_3,
      fixedXSubtotal_root1_4, fixedXSubtotal_root1_5,
      fixedXSubtotal_root1_6, fixedXSubtotal_root1_7,
      fixedXSubtotal_root1_8, fixedXSubtotal_root1_9,
      fixedXSubtotal_root1_10, fixedXSubtotal_root1_11,
      fixedXSubtotal_root1_12, fixedXSubtotal_root1_13,
      fixedXSubtotal_root1_14, fixedXSubtotal_root1_15,
      fixedXSubtotal_root1_16]
  · exact constantPartition_eq
  · exact constantPartition_eq
  · change partitionNumerator (4 : Fin 6) = 282088041119429551885567349491709846499805
    rw [partitionNumerator_eq_sum_fixedXSubtotal]
    rw [hRange]
    norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fixedXSubtotal_root4_0, fixedXSubtotal_root4_1,
      fixedXSubtotal_root4_2, fixedXSubtotal_root4_3,
      fixedXSubtotal_root4_4, fixedXSubtotal_root4_5,
      fixedXSubtotal_root4_6, fixedXSubtotal_root4_7,
      fixedXSubtotal_root4_8, fixedXSubtotal_root4_9,
      fixedXSubtotal_root4_10, fixedXSubtotal_root4_11,
      fixedXSubtotal_root4_12, fixedXSubtotal_root4_13,
      fixedXSubtotal_root4_14, fixedXSubtotal_root4_15,
      fixedXSubtotal_root4_16]
  · change partitionNumerator (5 : Fin 6) = 407013735975715118615493469577801822336350
    rw [partitionNumerator_eq_sum_fixedXSubtotal]
    rw [hRange]
    norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fixedXSubtotal_root5_0, fixedXSubtotal_root5_1,
      fixedXSubtotal_root5_2, fixedXSubtotal_root5_3,
      fixedXSubtotal_root5_4, fixedXSubtotal_root5_5,
      fixedXSubtotal_root5_6, fixedXSubtotal_root5_7,
      fixedXSubtotal_root5_8, fixedXSubtotal_root5_9,
      fixedXSubtotal_root5_10, fixedXSubtotal_root5_11,
      fixedXSubtotal_root5_12, fixedXSubtotal_root5_13,
      fixedXSubtotal_root5_14, fixedXSubtotal_root5_15,
      fixedXSubtotal_root5_16]

end MatrixMultiplication.Generated.LegalHybridQ20RootDualData
