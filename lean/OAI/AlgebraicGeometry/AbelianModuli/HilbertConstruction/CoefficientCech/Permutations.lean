/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.RepeatedTuplePartners

/-! # Permutations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.Permutations

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- Reindex native Cech cochains by a permutation of tuple positions. -/
noncomputable def coefficientCechPermutationF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex ρ M U).X n :=
  ((FormalCoproduct.evalOp X.Opens
    (ModuleCat.{u} R)).obj
      (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M)).map
        ((FormalCoproduct.mk _ U).mapPower σ).op

theorem coefficientCechPermutationF_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ τ : Equiv.Perm (Fin (n + 1))) :
    coefficientCechPermutationF ρ M U n σ ≫
        coefficientCechPermutationF ρ M U n τ =
      coefficientCechPermutationF ρ M U n (σ.trans τ) := by
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} R :=
    ((FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} R)).obj
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M))
  change F.map ((FormalCoproduct.mk _ U).mapPower σ).op ≫
      F.map ((FormalCoproduct.mk _ U).mapPower τ).op =
    F.map ((FormalCoproduct.mk _ U).mapPower (σ.trans τ)).op
  rw [← F.map_comp, ← op_comp]
  congr 1

theorem coefficientCechCoface_comp_permutation
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    OrderedCech.FormalProjection.coefficientCechCoface ρ M U n r ≫
        coefficientCechPermutationF ρ M U (n + 1) σ =
      coefficientCechPermutationF ρ M U n (Cech.PermutedTupleSigns.cechPermDelete σ r) ≫
        OrderedCech.FormalProjection.coefficientCechCoface ρ M U n (σ r) := by
  let V := FormalCoproduct.mk _ U
  let F : (FormalCoproduct.{u} X.Opens)ᵒᵖ ⥤
      ModuleCat.{u} R :=
    ((FormalCoproduct.evalOp X.Opens
      (ModuleCat.{u} R)).obj
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M))
  change F.map (V.mapPower r.succAbove).op ≫
      F.map (V.mapPower σ).op =
    F.map (V.mapPower (Cech.PermutedTupleSigns.cechPermDelete σ r)).op ≫
      F.map (V.mapPower (σ r).succAbove).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  congr 1
  rw [← FormalCoproduct.mapPower_comp,
    ← FormalCoproduct.mapPower_comp]
  have hfun : σ ∘ r.succAbove =
      (σ r).succAbove ∘ Cech.PermutedTupleSigns.cechPermDelete σ r := by
    funext x
    exact (Cech.PermutedTupleSigns.succAbove_cechPermDelete σ r x).symm
  exact congrArg (fun q => q.op) (congrArg
    (fun f : Fin (n + 1) → Fin (n + 2) => V.mapPower f) hfun)

theorem coefficientCechPermutationF_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1) → ι) :
    coefficientCechPermutationF ρ M U n σ ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i =
      Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) (i ∘ σ) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ i).op := by
  change (Pi.lift fun j : Fin (n + 1) → ι =>
      Pi.π (fun k : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n k) (j ∘ σ) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map
          (((FormalCoproduct.mk _ U).mapPower σ).φ j).op) ≫ _ = _
  exact Pi.lift_comp_π _ i

theorem coefficientCechXIsoPi_hom_comp_proj
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).hom ≫
        ModuleCat.ofHom
          (LinearMap.proj i :
            (∀ j : Fin (n + 1) → ι, Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) →ₗ[
              R] Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i) =
      Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i := by
  exact ModuleCat.piIsoPi_hom_ker_subtype _ i

theorem orderedCoefficientCechZeroExtendLinearMap_apply
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : Ordered.CoefficientCechTerms.orderedCoefficientCechTerm ρ M U n) (i : Fin (n + 1) → ι) :
    OrderedCech.ProjectionCoordinates.orderedCoefficientCechZeroExtendLinearMap ρ M U n x i =
      if h : StrictMono i then x ⟨i, h⟩ else 0 := by
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.Permutations
