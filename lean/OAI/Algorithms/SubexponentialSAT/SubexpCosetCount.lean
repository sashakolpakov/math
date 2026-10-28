import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CosetCardinality
import OAI.Algorithms.SubexponentialSAT.SubexpDirectSums

namespace OAI.Algorithms

/-!
# Exact multi-color coset counts and their exponent bound

This file proves the cardinality calculation in (1.1) and (4.7) of the
subexponential manuscript. Every color count and field size remains a parameter.
The count concerns actual finite quotient classes and points in their cosets;
it is not a theorem about the bit cost of constructing or enumerating them.
-/

namespace SubexponentialSAT.SubexpCosetCount

open scoped BigOperators
open Module
open SubexponentialSAT.CosetCardinality

instance finiteCosetFiber {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W]
    [Module 𝔽 W] [Finite W] (K : Submodule 𝔽 W) (q : W ⧸ K) :
    Finite (CosetFiber K q) := by
  unfold CosetFiber
  infer_instance

/-- The exponent coefficient in the manuscript. -/
noncomputable def alpha (r : ℕ) (τ : ℝ) : ℝ :=
  1 - (1 - τ) ^ 2 + 1 / (r : ℝ)

/-- Outer choices times the total number of inner-sum terms per outer choice. -/
def iterationCount {r : ℕ} (p D : ℕ) (d : Fin r → ℕ) : ℕ :=
  p ^ (D - ∑ g, d g) * ∑ g, p ^ d g

/-- Distribution over colors gives one power per color. -/
theorem iterationCount_eq_sum {r : ℕ} (p D : ℕ) (d : Fin r → ℕ) :
    iterationCount p D d = ∑ g, p ^ (D - ∑ h, d h + d g) := by
  simp only [iterationCount, Finset.mul_sum, pow_add]

/-- The total-dimension and maximum-dimension hypotheses bound each exponent.
No rounding of `D/r` or `(1-τ)^2 D` is implicit: these are real inequalities. -/
theorem exponent_le_alpha {r D : ℕ} (d : Fin r → ℕ) (τ : ℝ)
    (hsum : ∑ g, d g ≤ D)
    (hlower : (1 - τ) ^ 2 * (D : ℝ) ≤ ∑ g, (d g : ℝ))
    (hupper : ∀ g, (d g : ℝ) ≤ (D : ℝ) / (r : ℝ)) (g : Fin r) :
    ((D - ∑ h, d h + d g : ℕ) : ℝ) ≤ alpha r τ * (D : ℝ) := by
  rw [Nat.cast_add, Nat.cast_sub hsum, Nat.cast_sum]
  calc
    (D : ℝ) - ∑ h, (d h : ℝ) + (d g : ℝ) ≤
        (D : ℝ) - (1 - τ) ^ 2 * D + (D : ℝ) / r :=
      add_le_add (sub_le_sub_left hlower (D : ℝ)) (hupper g)
    _ = alpha r τ * (D : ℝ) := by
      unfold alpha
      ring

/-- The exact integer count satisfies the claimed real-exponent bound.
This even holds when `r=0` (both counts are zero); applications use `r ≥ 2`. -/
theorem iterationCount_le_real {r : ℕ} (p D : ℕ) (d : Fin r → ℕ) (τ : ℝ)
    (hp : 1 ≤ p) (hsum : ∑ g, d g ≤ D)
    (hlower : (1 - τ) ^ 2 * (D : ℝ) ≤ ∑ g, (d g : ℝ))
    (hupper : ∀ g, (d g : ℝ) ≤ (D : ℝ) / (r : ℝ)) :
    (iterationCount p D d : ℝ) ≤
      (r : ℝ) * (p : ℝ) ^ (alpha r τ * (D : ℝ)) := by
  rw [iterationCount_eq_sum]
  simp only [Nat.cast_sum, Nat.cast_pow]
  calc
    ∑ g, (p : ℝ) ^ (D - ∑ h, d h + d g) ≤
        ∑ _g : Fin r, (p : ℝ) ^ (alpha r τ * (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro g _
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hp) (exponent_le_alpha d τ hsum hlower hupper g)
    _ = (r : ℝ) * (p : ℝ) ^ (alpha r τ * (D : ℝ)) := by
      simp

section Families

variable {r : ℕ} {𝔽 Vstar : Type*} {V : Fin r → Type*}
  [Field 𝔽] [Fintype 𝔽] [AddCommGroup Vstar] [Module 𝔽 Vstar] [Fintype Vstar]
  [∀ g, AddCommGroup (V g)] [∀ g, Module 𝔽 (V g)] [∀ g, Fintype (V g)]

/-- One complement vector and a quotient class for each color. -/
abbrev OuterData (K : ∀ g, Submodule 𝔽 (V g)) :=
  Vstar × ∀ g, V g ⧸ K g

/-- Choosing a color and a point in that color's actual coset describes one
term to be accumulated among the separate inner sums. -/
abbrev InnerData (K : ∀ g, Submodule 𝔽 (V g))
    (o : OuterData (Vstar := Vstar) K) :=
  Σ g, CosetFiber (K g) (o.2 g)

/-- All actual inner-sum terms for all actual outer choices. -/
abbrev IterationData (K : ∀ g, Submodule 𝔽 (V g)) :=
  Σ o : OuterData (Vstar := Vstar) K, InnerData K o

/-- The complement vector and all quotient classes of a split assignment. -/
def outerMap (K : ∀ g, Submodule 𝔽 (V g)) (x : Vstar × ∀ g, V g) :
    OuterData (Vstar := Vstar) K :=
  (x.1, fun g => Submodule.Quotient.mk (x.2 g))

/-- The fiber of `outerMap` consists precisely of one point in each given coset. -/
def outerMapFiberEquiv (K : ∀ g, Submodule 𝔽 (V g))
    (o : OuterData (Vstar := Vstar) K) :
    {x : Vstar × ∀ g, V g // outerMap K x = o} ≃
      (∀ g, CosetFiber (K g) (o.2 g)) where
  toFun x g := ⟨x.val.2 g, congrFun (congrArg Prod.snd x.property) g⟩
  invFun x := ⟨(o.1, fun g => (x g).val), by
    change (o.1, fun g => (Submodule.Quotient.mk (x g).val : V g ⧸ K g)) = o
    apply Prod.ext
    · rfl
    · funext g
      exact (x g).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Prod.fst x.property).symm
    · rfl
  right_inv x := by
    funext g
    apply Subtype.ext
    rfl

/-- The exact multi-color quotient/coset decomposition of all split assignments.
Compose this with the disjoint-coordinate linear equivalence to obtain the
decomposition of the original full coordinate space. -/
def familyCosetEquiv (K : ∀ g, Submodule 𝔽 (V g)) :
    (Vstar × ∀ g, V g) ≃
      Σ o : OuterData (Vstar := Vstar) K, ∀ g, CosetFiber (K g) (o.2 g) :=
  (Equiv.sigmaFiberEquiv (outerMap (Vstar := Vstar) K)).symm.trans
    (Equiv.sigmaCongrRight (outerMapFiberEquiv K))

omit [Fintype 𝔽] [AddCommGroup Vstar] [Module 𝔽 Vstar] [Fintype Vstar]
  [∀ g, Fintype (V g)] in
@[simp]
theorem familyCosetEquiv_symm_apply (K : ∀ g, Submodule 𝔽 (V g))
    (o : OuterData (Vstar := Vstar) K) (x : ∀ g, CosetFiber (K g) (o.2 g)) :
    (familyCosetEquiv K).symm ⟨o, x⟩ = (o.1, fun g => (x g).val) := rfl

/-- The complement dimension plus all coordinate-block dimensions. -/
noncomputable def ambientDimension : ℕ :=
  finrank 𝔽 Vstar + ∑ g, finrank 𝔽 (V g)

omit [Fintype 𝔽] [Fintype Vstar] in
/-- The sum of the inner dimensions cannot exceed the ambient dimension. -/
theorem sum_dimensions_le (K : ∀ g, Submodule 𝔽 (V g)) :
    ∑ g, finrank 𝔽 (K g) ≤ ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) := by
  have hsum : (∑ g, finrank 𝔽 (V g ⧸ K g)) + (∑ g, finrank 𝔽 (K g)) =
      ∑ g, finrank 𝔽 (V g) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => (K g).finrank_quotient_add_finrank)
  unfold ambientDimension
  omega

omit [Fintype 𝔽] in
/-- Any linear splitting of the ambient space identifies its dimension with
the complement-plus-block dimension used in the cardinality formulas. -/
theorem ambientDimension_eq_finrank {W : Type*} [AddCommGroup W] [Module 𝔽 W]
    (e : W ≃ₗ[𝔽] (Vstar × ∀ g, V g)) :
    ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) = finrank 𝔽 W := by
  rw [e.finrank_eq]
  simp only [ambientDimension, Module.finrank_prod, Module.finrank_pi_fintype]

omit [Fintype 𝔽] in
/-- Specialization for an actual finite coordinate space. It lets the
disjoint-support splitting module supply `D` without an extra dimension axiom. -/
theorem ambientDimension_eq_card_coordinates {ι : Type*} [Fintype ι]
    (e : (ι → 𝔽) ≃ₗ[𝔽] (Vstar × ∀ g, V g)) :
    ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) = Fintype.card ι := by
  rw [ambientDimension_eq_finrank e, Module.finrank_fintype_fun_eq_card]

/-- Exact number of quotient-class choices, with the complement included. -/
theorem card_outer (K : ∀ g, Submodule 𝔽 (V g)) :
    Nat.card (OuterData (Vstar := Vstar) K) =
      Fintype.card 𝔽 ^ (ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) -
        ∑ g, finrank 𝔽 (K g)) := by
  have hsum : (∑ g, finrank 𝔽 (V g ⧸ K g)) + (∑ g, finrank 𝔽 (K g)) =
      ∑ g, finrank 𝔽 (V g) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => (K g).finrank_quotient_add_finrank)
  have hprod : (∏ g, Nat.card (V g ⧸ K g)) =
      Fintype.card 𝔽 ^ (∑ g, finrank 𝔽 (V g ⧸ K g)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro g _
    simpa only [Nat.card_eq_fintype_card] using
      (SubexponentialSAT.CosetCardinality.card_module (𝔽 := 𝔽) (V := V g ⧸ K g))
  rw [Nat.card_prod, Nat.card_pi, hprod]
  rw [SubexponentialSAT.CosetCardinality.card_module (𝔽 := 𝔽) (V := Vstar)]
  simp only [Nat.card_eq_fintype_card]
  rw [← pow_add]
  congr 1
  unfold ambientDimension
  omega

omit [AddCommGroup Vstar] [Module 𝔽 Vstar] [Fintype Vstar] in
/-- Every color contributes exactly a field-size power to the inner term count. -/
theorem card_inner (K : ∀ g, Submodule 𝔽 (V g))
    (o : OuterData (Vstar := Vstar) K) :
    Nat.card (InnerData K o) = ∑ g, Fintype.card 𝔽 ^ finrank 𝔽 (K g) := by
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro g _
  simpa only [Nat.card_eq_fintype_card] using card_coset (K g) (o.2 g)

/-- Exact cardinality of the actual dependent iteration type. -/
theorem card_iteration (K : ∀ g, Submodule 𝔽 (V g)) :
    Nat.card (IterationData (Vstar := Vstar) K) =
      iterationCount (Fintype.card 𝔽)
        (ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V))
        (fun g => finrank 𝔽 (K g)) := by
  rw [Nat.card_sigma]
  simp_rw [card_inner]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_outer]
  rfl

/-- The manuscript's bound for actual coset enumeration, with all parameters
visible. Disjoint-support applications supply the two dimension estimates. -/
theorem card_iteration_le_real (K : ∀ g, Submodule 𝔽 (V g)) (τ : ℝ)
    (hlower : (1 - τ) ^ 2 *
      (ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) : ℝ) ≤
        ∑ g, (finrank 𝔽 (K g) : ℝ))
    (hupper : ∀ g, (finrank 𝔽 (K g) : ℝ) ≤
      (ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) : ℝ) / (r : ℝ)) :
    (Nat.card (IterationData (Vstar := Vstar) K) : ℝ) ≤
      (r : ℝ) * (Fintype.card 𝔽 : ℝ) ^
        (alpha r τ * (ambientDimension (𝔽 := 𝔽) (Vstar := Vstar) (V := V) : ℝ)) := by
  rw [card_iteration]
  exact iterationCount_le_real _ _ _ τ Fintype.card_pos
    (sum_dimensions_le (Vstar := Vstar) K) hlower hupper

end Families

section Coordinates

variable {r : ℕ} {𝔽 I : Type*} [Field 𝔽] [Fintype 𝔽] [Fintype I] [DecidableEq I]

/-- Outer data for the literal disjoint coordinate supports of the layout. -/
abbrev CoordinateOuterData (S : Fin r → Finset I)
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) :=
  OuterData (Vstar := ↥((Finset.univ.biUnion S)ᶜ) → 𝔽) K

/-- Restrict coordinates and then record one quotient class and coset point
for every color. This partitions the original full assignment space exactly. -/
noncomputable def coordinateCosetEquiv (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) :
    (I → 𝔽) ≃ Σ o : CoordinateOuterData S K, ∀ g, CosetFiber (K g) (o.2 g) :=
  (SubexpDirectSums.coordinateSplitEquiv S hS).toEquiv.trans (familyCosetEquiv K)

/-- Reconstruction of an original assignment from all its coset data. -/
noncomputable def coordinateReconstruct (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (o : CoordinateOuterData S K)
    (x : ∀ g, CosetFiber (K g) (o.2 g)) : I → 𝔽 :=
  (coordinateCosetEquiv S hS K).symm ⟨o, x⟩

omit [Fintype 𝔽] in
/-- The concrete reconstruction is the complement extension plus the sum of
the zero extensions of the selected color vectors. -/
@[simp]
theorem coordinateReconstruct_eq (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (o : CoordinateOuterData S K)
    (x : ∀ g, CosetFiber (K g) (o.2 g)) :
    coordinateReconstruct S hS K o x =
      SubexpDirectSums.coordinateAssemble S (o.1, fun g => (x g).val) := rfl

omit [Fintype 𝔽] in
theorem coordinateReconstruct_eq_split_symm (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (o : CoordinateOuterData S K)
    (x : ∀ g, CosetFiber (K g) (o.2 g)) :
    coordinateReconstruct S hS K o x =
      (SubexpDirectSums.coordinateSplitEquiv S hS).symm (o.1, fun g => (x g).val) := rfl

omit [Fintype 𝔽] in
@[simp]
theorem coordinateReconstruct_on_color (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (o : CoordinateOuterData S K)
    (x : ∀ g, CosetFiber (K g) (o.2 g)) (g : Fin r) (i : S g) :
    coordinateReconstruct S hS K o x i.val = (x g).val i := by
  rw [coordinateReconstruct_eq]
  exact SubexpDirectSums.coordinateAssemble_on_color S hS _ g i.val i.property

omit [Fintype 𝔽] in
@[simp]
theorem coordinateReconstruct_outside (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (o : CoordinateOuterData S K)
    (x : ∀ g, CosetFiber (K g) (o.2 g)) (i : ↥((Finset.univ.biUnion S)ᶜ)) :
    coordinateReconstruct S hS K o x i.val = o.1 i := by
  rw [coordinateReconstruct_eq]
  exact SubexpDirectSums.coordinateAssemble_outside S _ i.val i.property

omit [Fintype 𝔽] in
/-- The coordinate splitting supplies the ambient-dimension equality. -/
theorem coordinate_ambientDimension (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h)) :
    ambientDimension (𝔽 := 𝔽) (Vstar := ↥((Finset.univ.biUnion S)ᶜ) → 𝔽)
      (V := fun g => S g → 𝔽) = Fintype.card I := by
  simpa only [ambientDimension, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    SubexpDirectSums.coordinate_card_partition S hS

theorem card_coordinate_outer (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) :
    Nat.card (CoordinateOuterData S K) =
      Fintype.card 𝔽 ^ (Fintype.card I - ∑ g, finrank 𝔽 (K g)) := by
  rw [card_outer, coordinate_ambientDimension S hS]

theorem card_coordinate_iteration (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) :
    Nat.card (IterationData (Vstar := ↥((Finset.univ.biUnion S)ᶜ) → 𝔽) K) =
      iterationCount (Fintype.card 𝔽) (Fintype.card I) (fun g => finrank 𝔽 (K g)) := by
  rw [card_iteration, coordinate_ambientDimension S hS]

/-- The complete exact-coset-to-real-bound statement on the original
coordinate supports. Both dimension estimates are explicit hypotheses. -/
theorem card_coordinate_iteration_le_real (S : Fin r → Finset I)
    (hS : Pairwise fun g h => Disjoint (S g) (S h))
    (K : ∀ g, Submodule 𝔽 (S g → 𝔽)) (τ : ℝ)
    (hlower : (1 - τ) ^ 2 * (Fintype.card I : ℝ) ≤ ∑ g, (finrank 𝔽 (K g) : ℝ))
    (hupper : ∀ g, (finrank 𝔽 (K g) : ℝ) ≤ (Fintype.card I : ℝ) / (r : ℝ)) :
    (Nat.card (IterationData (Vstar := ↥((Finset.univ.biUnion S)ᶜ) → 𝔽) K) : ℝ) ≤
      (r : ℝ) * (Fintype.card 𝔽 : ℝ) ^ (alpha r τ * (Fintype.card I : ℝ)) := by
  have hsum := sum_dimensions_le (Vstar := ↥((Finset.univ.biUnion S)ᶜ) → 𝔽) K
  rw [coordinate_ambientDimension S hS] at hsum
  rw [card_coordinate_iteration S hS]
  exact iterationCount_le_real _ _ _ τ Fintype.card_pos hsum hlower hupper

end Coordinates

end SubexponentialSAT.SubexpCosetCount

end OAI.Algorithms
