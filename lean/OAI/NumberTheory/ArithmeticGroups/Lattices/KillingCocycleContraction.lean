import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantDualTensor
import Mathlib.Algebra.Lie.Cochain

/-! # Killing Cocycle Contraction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingCocycleContraction.Construction

noncomputable section

section

/-! An explicit contraction of adjoint-valued two-cocycles for a
finite-dimensional Lie algebra with nondegenerate Killing form. -/

open scoped Classical
open _root_.Module LieAlgebra

attribute [local instance] LieRing.ofAssociativeRing

def killingCocycleContraction
    {k L ι : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Fintype ι]
    (hB : (killingForm k L).Nondegenerate) (b : Basis ι k L)
    (φ : L →ₗ[k] L →ₗ[k] L) : L →ₗ[k] L :=
  ∑ i, (ad k L (b i)).comp (φ ((killingForm k L).dualBasis hB b i))

theorem killing_contraction_lie
    {k L ι : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Fintype ι]
    (hB : (killingForm k L).Nondegenerate) (b : Basis ι k L)
    (φ : L →ₗ[k] L →ₗ[k] L) (x y : L) :
    (∑ i, ⁅x, ⁅b i, φ ((killingForm k L).dualBasis hB b i) y⁆⁆) =
      ∑ i, ⁅b i, ⁅x, φ ((killingForm k L).dualBasis hB b i) y⁆ -
        φ ⁅x, (killingForm k L).dualBasis hB b i⁆ y⁆ := by
  let d := (killingForm k L).dualBasis hB b
  have hd : (∑ i, ⁅⁅x, b i⁆, φ (d i) y⁆) + (∑ i, ⁅b i, φ ⁅x, d i⁆ y⁆) = 0 :=
    InvariantDualTensor.Construction.killing_dualBasis_lie_sum hB b x ((ad k L).toLinearMap.compl₂ (φ.flip y))
  have hm : (∑ i, ⁅⁅x, b i⁆, φ (d i) y⁆) = -(∑ i, ⁅b i, φ ⁅x, d i⁆ y⁆) :=
    eq_neg_iff_add_eq_zero.mpr hd
  change (∑ i, ⁅x, ⁅b i, φ (d i) y⁆⁆) = ∑ i, ⁅b i, ⁅x, φ (d i) y⁆ - φ ⁅x, d i⁆ y⁆
  calc
    _ = ∑ i, (⁅⁅x, b i⁆, φ (d i) y⁆ + ⁅b i, ⁅x, φ (d i) y⁆⁆) := by
      apply Finset.sum_congr rfl
      intro i _
      exact leibniz_lie x (b i) (φ (d i) y)
    _ = _ := by
      simp only [lie_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hm]
      abel

theorem killing_cocycle_contraction_coboundary
    {k L ι : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Fintype ι]
    (hB : (killingForm k L).Nondegenerate) (b : Basis ι k L)
    (φ : L →ₗ[k] L →ₗ[k] L) (hskew : ∀ x y, φ x y = -φ y x)
    (hcoc : ∀ x y z, ⁅x, φ y z⁆ - ⁅y, φ x z⁆ + ⁅z, φ x y⁆ -
      φ ⁅x, y⁆ z + φ ⁅x, z⁆ y - φ ⁅y, z⁆ x = 0) (x y : L) :
    ⁅x, killingCocycleContraction hB b φ y⁆ - ⁅y, killingCocycleContraction hB b φ x⁆ -
      killingCocycleContraction hB b φ ⁅x, y⁆ = φ x y := by
  let d := (killingForm k L).dualBasis hB b
  have hc (i : ι) : (⁅x, φ (d i) y⁆ - φ ⁅x, d i⁆ y) -
      (⁅y, φ (d i) x⁆ - φ ⁅y, d i⁆ x) - φ (d i) ⁅x, y⁆ = ⁅d i, φ x y⁆ := by
    have h := hcoc (d i) x y
    rw [← lie_skew (d i) x, ← lie_skew (d i) y, map_neg, LinearMap.neg_apply,
      map_neg, LinearMap.neg_apply, hskew ⁅x, y⁆ (d i)] at h
    apply sub_eq_zero.mp
    convert congrArg (fun z : L => -z) h using 1 <;> abel
  simp only [killingCocycleContraction, LinearMap.sum_apply, LinearMap.comp_apply, ad_apply, lie_sum]
  rw [killing_contraction_lie hB b φ x y, killing_contraction_lie hB b φ y x,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, ⁅b i, ⁅d i, φ x y⁆⁆ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← lie_sub, ← lie_sub, hc i]
    _ = φ x y := InvariantDualTensor.Construction.killing_casimir_apply hB b (φ x y)

end

/-! Adjoint-valued second cohomology vanishes when the Killing form
is nondegenerate. The proof supplies an explicit coboundary. -/

open scoped Classical
open _root_.Module LieModule.Cohomology

theorem killing_twoCocycle_is_coboundary
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (hB : (killingForm k L).Nondegenerate) (c : twoCocycle k L L) :
    ∃ T : L →ₗ[k] L, d₁₂ k L L T = c.val := by
  let b := Module.finBasis k L
  let φ := c.val.val
  have hs : ∀ x y, φ x y = -φ y x := fun x y => (twoCochain_skew c.val y x).symm
  have hc : ∀ x y z, ⁅x, φ y z⁆ - ⁅y, φ x z⁆ + ⁅z, φ x y⁆ -
      φ ⁅x, y⁆ z + φ ⁅x, z⁆ y - φ ⁅y, z⁆ x = 0 := by
    intro x y z
    exact congrArg (fun f : L →ₗ[k] L →ₗ[k] L →ₗ[k] L => f x y z) c.property
  refine ⟨killingCocycleContraction hB b φ, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact killing_cocycle_contraction_coboundary hB b φ hs hc x y

theorem killing_second_cocycle_kernel_eq_range
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (hB : (killingForm k L).Nondegenerate) :
    (d₂₃ k L L).ker = (d₁₂ k L L).range := by
  apply le_antisymm
  · intro c hc
    exact killing_twoCocycle_is_coboundary hB ⟨c, hc⟩
  · rintro _ ⟨T, rfl⟩
    have h := congrArg (fun f => (f : (L →ₗ[k] L) →ₗ[k] L →ₗ[k] L →ₗ[k] L →ₗ[k] L) T)
      (d₂₃_comp_d₁₂ k L L)
    exact h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingCocycleContraction.Construction
