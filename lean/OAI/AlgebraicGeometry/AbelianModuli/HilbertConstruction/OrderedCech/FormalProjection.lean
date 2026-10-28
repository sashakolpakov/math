/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.CoefficientCechComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex

/-! # Formal Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FormalProjection

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- The ordered intersection family includes in the all-tuples intersection family. -/
noncomputable def orderedCechFormalInclusion {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Ordered.SectionCechIndices.orderedCechFormalObject U n ⟶
      (FormalCoproduct.mk _ U).power (Fin (n + 1)) where
  f i := i.1
  φ _ := 𝟙 _

theorem orderedCechFace_comp_formalInclusion {X : Scheme.{u}}
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    Ordered.SectionCechIndices.orderedCechFace U n k ≫ orderedCechFormalInclusion U n =
      orderedCechFormalInclusion U (n + 1) ≫
        (FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun := by
  apply FormalCoproduct.hom_ext rfl
  intro i
  exact Subsingleton.elim _ _

/-- A native Cech coface before taking the alternating sum. -/
noncomputable def coefficientCechCoface {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X (n + 1) :=
  ((FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ U).cech).obj (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).δ k

theorem coefficientCechCoface_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (k : Fin (n + 2)) (i : Fin (n + 2) → ι) :
    coefficientCechCoface ρ M U n k ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U (n + 1) j) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j)
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  change (Pi.lift fun j : Fin (n + 2) → ι =>
      Pi.π (fun l : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n l)
          (j ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ j).op) ≫ _ = _
  exact Pi.lift_comp_π _ i

/-- Projection from all tuple components to strictly increasing components. -/
noncomputable def coefficientCechToOrderedF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n ⟶ Ordered.CoefficientCechTerms.orderedCoefficientCechObject ρ M U n :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} R)).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).map (orderedCechFormalInclusion U n).op

theorem coefficientCechCoface_comp_coefficientCechToOrderedF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (n : ℕ) (k : Fin (n + 2)) :
    coefficientCechCoface ρ M U n k ≫ coefficientCechToOrderedF ρ M U (n + 1) =
      coefficientCechToOrderedF ρ M U n ≫ Ordered.CoefficientCechTerms.orderedCoefficientCechCoface ρ M U n k := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} R :=
    ((FormalCoproduct.evalOp.{u} X.Opens
      (ModuleCat.{u} R)).obj
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M))
  change F.map ((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).op ≫
      F.map (orderedCechFormalInclusion U (n + 1)).op =
    F.map (orderedCechFormalInclusion U n).op ≫
      F.map (Ordered.SectionCechIndices.orderedCechFace U n k).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
    orderedCechFace_comp_formalInclusion U n k]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.FormalProjection
