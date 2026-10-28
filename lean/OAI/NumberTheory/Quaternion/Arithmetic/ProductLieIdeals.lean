import OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity
import Mathlib.Algebra.Lie.DirectSum

/-! # Product Lie Ideals -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals

noncomputable section

section

/-! An ideal in a direct sum of simple Lie algebras contains every factor
on which its projection is nonzero. This rules out coupled proper ideals
when passing from one local factor to a finite product. -/

open scoped Classical DirectSum

variable {κ ι : Type*} [CommRing κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra κ (L i)]

theorem directSum_lie_single_left (i : ι) (z : L i) (x : ⨁ j, L j) :
    ⁅DirectSum.of L i z, x⁆ = DirectSum.of L i ⁅z, x i⁆ := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp only [DirectSum.bracket_apply, DirectSum.of_eq_of_ne _ _ _ h, zero_lie]

theorem simple_lie_center_eq_bot (M : Type*) [LieRing M] [LieAlgebra κ M]
    [LieAlgebra.IsSimple κ M] : LieAlgebra.center κ M = ⊥ := by
  apply (LieAlgebra.IsSimple.eq_bot_or_eq_top (LieAlgebra.center κ M)).resolve_right
  intro hc
  exact LieAlgebra.IsSimple.non_abelian κ ((LieAlgebra.isLieAbelian_iff_center_eq_top κ M).mpr hc)

theorem directSum_axis_comap_eq_top (I : LieIdeal κ (⨁ j, L j)) (i : ι)
    [LieAlgebra.IsSimple κ (L i)] (hi : ∃ x ∈ I, x i ≠ 0) :
    I.comap (DirectSum.lieAlgebraOf κ ι L i) = ⊤ := by
  apply (LieAlgebra.IsSimple.eq_bot_or_eq_top (I.comap (DirectSum.lieAlgebraOf κ ι L i))).resolve_left
  intro hbot
  obtain ⟨x, hx, hxi⟩ := hi
  have hc : x i ∈ LieAlgebra.center κ (L i) := by
    apply (LieModule.mem_maxTrivSubmodule κ (L i) (L i) (x i)).mpr
    intro z
    have hb : ⁅z, x i⁆ ∈ I.comap (DirectSum.lieAlgebraOf κ ι L i) := by
      change DirectSum.of L i ⁅z, x i⁆ ∈ I
      rw [← directSum_lie_single_left]
      exact I.lie_mem hx
    rwa [hbot, LieSubmodule.mem_bot] at hb
  rw [simple_lie_center_eq_bot (κ := κ) (L i), LieSubmodule.mem_bot] at hc
  exact hxi hc

theorem directSum_ideal_eq_top_of_nonzero_projections
    [∀ i, LieAlgebra.IsSimple κ (L i)] (I : LieIdeal κ (⨁ j, L j))
    (hi : ∀ i, ∃ x ∈ I, x i ≠ 0) : I = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact I.zero_mem
  | add x y hx hy => exact I.add_mem hx hy
  | of i z =>
    have h : z ∈ I.comap (DirectSum.lieAlgebraOf κ ι L i) := by
      rw [directSum_axis_comap_eq_top I i (hi i)]
      trivial
    exact h

theorem invariant_subalgebra_eq_of_simple_factor_projections
    [∀ i, LieAlgebra.IsSimple κ (L i)]
    {A : Type*} [LieRing A] [LieAlgebra κ A]
    (J B : LieSubalgebra κ A) (hJB : J ≤ B)
    (e : B ≃ₗ⁅κ⁆ ⨁ j, L j)
    (hbracket : ∀ x y : A, x ∈ B → y ∈ J → ⁅x, y⁆ ∈ J)
    (hproj : ∀ i, ∃ x : B, x.val ∈ J ∧ e x i ≠ 0) : J = B := by
  obtain ⟨I, hI⟩ := (LieSubalgebra.exists_nested_lieIdeal_coe_eq_iff κ J hJB).mpr hbracket
  have hmap : I.map e.toLieHom = ⊤ := by
    apply directSum_ideal_eq_top_of_nonzero_projections
    intro i
    obtain ⟨x, hx, hxi⟩ := hproj i
    have hxI : x ∈ I := by
      change x ∈ I.toLieSubalgebra
      rw [hI, LieSubalgebra.mem_ofLe]
      exact hx
    refine ⟨e x, ?_, hxi⟩
    exact LieIdeal.mem_map hxI
  apply le_antisymm hJB
  intro x hx
  let b : B := ⟨x, hx⟩
  have hb : e b ∈ I.map e.toLieHom := by rw [hmap]; trivial
  obtain ⟨c, hcb⟩ := LieIdeal.mem_map_of_surjective e.surjective hb
  have hc := c.property
  have heq : c.val = b := e.injective hcb
  rw [heq] at hc
  change b ∈ I.toLieSubalgebra at hc
  rw [hI, LieSubalgebra.mem_ofLe] at hc
  exact hc

end

/-! Finite products of Lie subalgebras and their simple-factor ideal
criterion. The componentwise Lie instances are scoped explicitly. -/

open scoped Classical DirectSum

namespace LieProducts

scoped instance piLieRing {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i => add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i => lie_add (x i) (y i) (z i)
  lie_self x := funext fun i => lie_self (x i)
  leibniz_lie x y z := funext fun i => leibniz_lie (x i) (y i) (z i)

scoped instance piLieAlgebra {κ ι : Type*} [CommRing κ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra κ (L i)] : LieAlgebra κ (∀ i, L i) where
  lie_smul c x y := funext fun i => lie_smul c (x i) (y i)

end LieProducts
open scoped OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals.LieProducts

variable {κ ι : Type*} [CommRing κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra κ (L i)]

def directSumPiLieEquiv [Fintype ι] : (⨁ i, L i) ≃ₗ⁅κ⁆ (∀ i, L i) :=
  { DirectSum.linearEquivFunOnFintype κ ι L with map_lie' := rfl }

def piLieSubalgebra (B : ∀ i, LieSubalgebra κ (L i)) : LieSubalgebra κ (∀ i, L i) :=
  { Submodule.pi Set.univ (fun i => (B i).toSubmodule) with
    lie_mem' := fun hx hy i _ => (B i).lie_mem (hx i (Set.mem_univ i)) (hy i (Set.mem_univ i)) }

def piLieSubalgebraEquiv (B : ∀ i, LieSubalgebra κ (L i)) :
    piLieSubalgebra B ≃ₗ⁅κ⁆ (∀ i, B i) where
  toFun x i := ⟨x.val i, x.property i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).val, fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

theorem pi_invariant_subalgebra_eq [Fintype ι]
    (B : ∀ i, LieSubalgebra κ (L i)) [∀ i, LieAlgebra.IsSimple κ (B i)]
    (J : LieSubalgebra κ (∀ i, L i)) (hJB : J ≤ piLieSubalgebra B)
    (hbracket : ∀ x y, x ∈ piLieSubalgebra B → y ∈ J → ⁅x, y⁆ ∈ J)
    (hproj : ∀ i, ∃ x ∈ J, x i ≠ 0) : J = piLieSubalgebra B := by
  let e := (piLieSubalgebraEquiv B).trans (directSumPiLieEquiv (κ := κ)).symm
  apply invariant_subalgebra_eq_of_simple_factor_projections J (piLieSubalgebra B) hJB e hbracket
  intro i
  obtain ⟨x, hx, hxi⟩ := hproj i
  refine ⟨⟨x, hJB hx⟩, hx, ?_⟩
  intro hz
  exact hxi (congrArg Subtype.val hz)

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductLieIdeals
