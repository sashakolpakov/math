import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SubgroupStability
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Subgroup Stability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SubgroupStability

noncomputable section

/-! Stability under an integral ring action is detected on a genuine
integer basis. This reduces the clopen parameter construction to
finitely many equations without reducing its all-coefficient scope. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

theorem relativeSubgroupStable_action_of_basis
    {S : Scheme.{0}} {g : ℕ} {R : Type*} [CommRing R]
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : ActionData.IntegralAction R A)
    {T : Over S} (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme T)
    {I : Type*} (b : Module.Basis I ℤ R)
    (h : ∀ i, SubgroupStability.RelativeSubgroupStable F (ρ.map (b i))) :
    ∀ r, SubgroupStability.RelativeSubgroupStable F (ρ.map r) := by
  intro r X t x hx
  let m : R →+ Additive (X ⟶ A.scheme) := {
    toFun := fun a => Additive.ofMul (x ≫ ρ.map a)
    map_zero' := by
      change x ≫ ρ.map 0 = 1
      rw [ρ.map_zero, MonObj.comp_one]
    map_add' := by
      intro a c
      change x ≫ ρ.map (a + c) = (x ≫ ρ.map a) * (x ≫ ρ.map c)
      rw [ρ.map_add, MonObj.comp_mul] }
  let L : Submodule ℤ R :=
    ((F.points X t).toAddSubgroup.toIntSubmodule).comap m.toIntLinearMap
  have hL : (⊤ : Submodule ℤ R) ≤ L := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i X t x hx
  exact hL (Submodule.mem_top : r ∈ (⊤ : Submodule ℤ R))

theorem relativeSubgroupStable_action_iff_basis
    {S : Scheme.{0}} {g : ℕ} {R : Type*} [CommRing R]
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : ActionData.IntegralAction R A)
    {T : Over S} (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme T)
    {I : Type*} (b : Module.Basis I ℤ R) :
    (∀ r, SubgroupStability.RelativeSubgroupStable F (ρ.map r)) ↔
      ∀ i, SubgroupStability.RelativeSubgroupStable F (ρ.map (b i)) :=
  ⟨fun h i => h (b i), relativeSubgroupStable_action_of_basis A ρ F b⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SubgroupStability
