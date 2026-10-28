/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZeroExtension

/-! # Alternating Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingExtension

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- Alternating extension from increasing tuples to all tuples. -/
noncomputable def orderedToCoefficientCechAlternatingF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Ordered.CoefficientCechTerms.orderedCoefficientCechObject ρ M U n ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
    (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
      Permutations.coefficientCechPermutationF ρ M U n σ)

theorem orderedToCoefficientCechAlternatingF_comp_permutation
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    orderedToCoefficientCechAlternatingF ρ M U n ≫
        Permutations.coefficientCechPermutationF ρ M U n τ =
      (Equiv.Perm.sign τ : ℤ) •
        orderedToCoefficientCechAlternatingF ρ M U n := by
  rw [orderedToCoefficientCechAlternatingF, sum_comp, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [zsmul_comp, Category.assoc, Permutations.coefficientCechPermutationF_comp,
    Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
  rw [show σ.trans τ = τ * σ by rfl]
  rw [Units.val_mul, ← mul_assoc, Int.units_coe_mul_self, one_mul]

theorem coefficientCechProjection_comp_map_eq_of_eq
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (j k : Fin (n + 1) → ι) (hjk : j = k) {V : X.Opens}
    (a : V ⟶ ∏ᶜ fun x : Fin (n + 1) => U (j x))
    (b : V ⟶ ∏ᶜ fun x : Fin (n + 1) => U (k x)) :
    Pi.π (fun q : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n q) j ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map a.op =
      Pi.π (fun q : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n q) k ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map b.op := by
  subst k
  rw [Subsingleton.elim a b]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingExtension
