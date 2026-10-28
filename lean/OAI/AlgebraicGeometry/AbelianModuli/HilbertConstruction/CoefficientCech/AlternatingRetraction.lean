/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PairCancellation

/-! # Alternating Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingRetraction

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_π_of_not_injective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ Function.Injective i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i = 0 := by
  let e : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ e = 0
  rw [AlternatingExtension.orderedToCoefficientCechAlternatingF, sum_comp]
  apply Finset.sum_eq_zero
  intro σ _
  rw [zsmul_comp, Category.assoc, Permutations.coefficientCechPermutationF_comp_π]
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ σ) :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ σ)
  let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ σ) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
  change (Equiv.Perm.sign σ : ℤ) •
    (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ p ≫ r) = 0
  have hmono : ¬ StrictMono (i ∘ σ) := by
    intro h
    apply hi
    intro a b hab
    apply σ.symm.injective
    apply h.injective
    simpa using hab
  have hz :
      OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ p = 0 := by
    dsimp only [p]
    exact ZeroExtension.orderedToCoefficientCechZeroExtensionF_comp_π_of_not_strictMono
      coefficientMap M U n (i ∘ σ) hmono
  have hpost :
      OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (p ≫ r) = 0 := by
    calc
      OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (p ≫ r) =
          (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ p) ≫ r :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hz, zero_comp]
  rw [hpost, smul_zero]

theorem coefficientCechPermutationF_one
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    Permutations.coefficientCechPermutationF coefficientMap M U n 1 = 𝟙 _ := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} R :=
    ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} R)).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M))
  change F.map
        ((FormalCoproduct.mk _ U).mapPower (id : Fin (n + 1) → Fin (n + 1))).op = _
  rw [FormalCoproduct.mapPower_id]
  exact F.map_id _

theorem orderedToCoefficientCechAlternatingF_comp_coefficientCechToOrderedF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n = 𝟙 _ := by
  rw [AlternatingExtension.orderedToCoefficientCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single 1]
  · simp [coefficientCechPermutationF_one,
      OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF_comp_coefficientCechToOrderedF]
  · intro σ hσ hne
    rw [zsmul_comp]
    simp [ZeroExtension.orderedToCoefficientCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
      coefficientMap M U n σ hne]
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingRetraction
