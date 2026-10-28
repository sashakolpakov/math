import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantSubmoduleEquivalence
import Mathlib.Topology.Algebra.Algebra.Equiv

/-! # Nilpotent Product Equivariance -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductEquivariance.Construction

noncomputable section

/-! Exponential product coordinates respect algebra automorphisms
preserving both complementary tangent subspaces. -/

open NormedSpace

def invariantSubmoduleProductHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E ≃L[ℝ] E) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, q x ∈ U) (hUi : ∀ x ∈ U, q.symm x ∈ U)
    (hV : ∀ x ∈ V, q x ∈ V) (hVi : ∀ x ∈ V, q.symm x ∈ V) : U × V ≃ₜ U × V :=
  (InvariantSubmoduleEquivalence.Construction.invariantSubmoduleEquiv q U hU hUi).toHomeomorph.prodCongr
    (InvariantSubmoduleEquivalence.Construction.invariantSubmoduleEquiv q V hV hVi).toHomeomorph

theorem exponentialProductCoordinates_equivariant
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W)
    (R : A ≃A[ℝ] A) (q : W ≃L[ℝ] W) (hq : ∀ x : W, (q x).val = R x.val)
    (hU : ∀ x ∈ U, q x ∈ U) (hUi : ∀ x ∈ U, q.symm x ∈ U)
    (hV : ∀ x ∈ V, q x ∈ V) (hVi : ∀ x ∈ V, q.symm x ∈ V)
    (p : U × V) :
    NilpotentProductDerivative.Construction.exponentialProductCoordinates W hmul hexp U V
      (invariantSubmoduleProductHomeomorph q U V hU hUi hV hVi p) =
      q (NilpotentProductDerivative.Construction.exponentialProductCoordinates W hmul hexp U V p) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Subtype.ext
  change exp (q p.1.val).val * exp (q p.2.val).val - 1 =
    (q (NilpotentProductDerivative.Construction.exponentialProductCoordinates W hmul hexp U V p)).val
  rw [hq, hq, hq]
  change exp (R p.1.val.val) * exp (R p.2.val.val) - 1 =
    R (exp p.1.val.val * exp p.2.val.val - 1)
  rw [map_sub, map_mul, map_one, map_exp R R.continuous, map_exp R R.continuous]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductEquivariance.Construction
