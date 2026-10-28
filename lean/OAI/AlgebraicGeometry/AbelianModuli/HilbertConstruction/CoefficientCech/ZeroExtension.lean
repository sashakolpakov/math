/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.Permutations

/-! # Zero Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZeroExtension

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechZeroExtensionF_comp_permutation_comp_ordered_of_ne
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ ≠ 1) :
    OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
        Permutations.coefficientCechPermutationF ρ M U n σ ≫
          OrderedCech.FormalProjection.coefficientCechToOrderedF ρ M U n = 0 := by
  apply (cancel_epi (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).inv).1
  apply (cancel_mono (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom).1
  rw [comp_zero, zero_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi : ¬ StrictMono (i.1 ∘ σ) := by
    intro h
    have hmono : Monotone σ := fun a b hab =>
      i.2.le_iff_le.mp (h.monotone hab)
    exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)
  have hcomp :
      (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).inv ≫
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
            Permutations.coefficientCechPermutationF ρ M U n σ ≫
              OrderedCech.FormalProjection.coefficientCechToOrderedF ρ M U n ≫
                (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom ≫
                  ModuleCat.ofHom (LinearMap.proj i) = 0 := by
    rw [OrderedCech.ProjectionCoordinates.orderedCoefficientCechObjectIsoPi_hom_comp_proj ρ M U n i,
      OrderedCech.ProjectionCoordinates.coefficientCechToOrderedF_comp_π ρ M U n i,
      Permutations.coefficientCechPermutationF_comp_π ρ M U n σ i.1]
    let e := Pi.π (fun j : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) (i.1 ∘ σ)
    let r : Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n (i.1 ∘ σ) ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i.1 :=
      (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i.1).op
    change (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).inv ≫
      OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫ e ≫ r = 0
    rw [OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hprefix :
        ModuleCat.ofHom (OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n) ≫
            (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ e = 0 := by
      dsimp only [e]
      rw [OrderedCech.ProjectionCoordinates.coefficientCechXIsoPi_inv_comp_proj ρ M U n (i.1 ∘ σ)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n y (i.1 ∘ σ) = 0
      rw [Permutations.orderedCoefficientCechZeroExtendLinearMap_apply, dite_eq_right hi]
    let a := ModuleCat.ofHom (OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n)
    calc
      a ≫ ((Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ (e ≫ r)) =
          a ≫ (((Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ e) ≫ r) :=
        congrArg (fun q => a ≫ q)
          (Category.assoc (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv e r).symm
      _ = (a ≫ ((Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ e)) ≫ r :=
        (Category.assoc a ((Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ e) r).symm
      _ = 0 := by rw [hprefix, zero_comp]
  have hx := ConcreteCategory.congr_hom hcomp x
  exact hx

theorem orderedToCoefficientCechZeroExtensionF_comp_π_of_not_strictMono
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : ¬ StrictMono i) :
    OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i = 0 := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i
  change OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫ p = 0
  have hlinear :
      ModuleCat.ofHom (OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n) ≫
          (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫ p = 0 := by
    dsimp only [p]
    rw [OrderedCech.ProjectionCoordinates.coefficientCechXIsoPi_inv_comp_proj]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n x i = 0
    rw [Permutations.orderedCoefficientCechZeroExtendLinearMap_apply, dite_eq_right hi]
  rw [OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF]
  simp only [Category.assoc, hlinear, comp_zero]

theorem orderedToCoefficientCechZeroExtensionF_comp_π_of_strictMono
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j.1) ⟨i, hi⟩ := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i
  let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject ρ M U n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i :=
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j.1) ⟨i, hi⟩
  have hp : OrderedCech.FormalProjection.coefficientCechToOrderedF ρ M U n ≫ q = p := by
    dsimp only [p, q]
    exact OrderedCech.ProjectionCoordinates.coefficientCechToOrderedF_comp_π ρ M U n ⟨i, hi⟩
  change OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫ p = q
  calc
    OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫ p =
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
          (OrderedCech.FormalProjection.coefficientCechToOrderedF ρ M U n ≫ q) :=
      congrArg (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫ ·) hp.symm
    _ = (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF ρ M U n ≫
          OrderedCech.FormalProjection.coefficientCechToOrderedF ρ M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF_comp_coefficientCechToOrderedF,
        Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZeroExtension
