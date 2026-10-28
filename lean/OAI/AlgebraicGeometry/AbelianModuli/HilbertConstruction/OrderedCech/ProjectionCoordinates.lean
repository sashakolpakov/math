/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ComplexProjection

/-! # Projection Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionCoordinates

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- Restriction of an all-tuples family to strictly increasing tuples. -/
noncomputable def coefficientCechPiToOrderedLinearMap
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (∀ i : Fin (n + 1) → ι, Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i) →ₗ[R]
      Ordered.CoefficientCechTerms.orderedCoefficientCechTerm ρ M U n :=
  LinearMap.pi fun i => LinearMap.proj i.1

/-- Extend a dependent family on a subtype by zero. -/
noncomputable def piSubtypeZeroExtend
    {R I : Type u} [Semiring R] (p : I → Prop) [DecidablePred p]
    (Z : I → Type u) [∀ i, AddCommMonoid (Z i)] [∀ i, Module R (Z i)] :
    (∀ i : Subtype p, Z i.1) →ₗ[R] ∀ i, Z i where
  toFun x i := if h : p i then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : p i <;> simp [h]
  map_smul' r x := by
    funext i
    by_cases h : p i <;> simp [h]

theorem piSubtypeRestriction_comp_zeroExtend
    {R I : Type u} [Semiring R] (p : I → Prop) [DecidablePred p]
    (Z : I → Type u) [∀ i, AddCommMonoid (Z i)] [∀ i, Module R (Z i)] :
    (LinearMap.pi fun i : Subtype p =>
      (LinearMap.proj i.1 : (∀ i, Z i) →ₗ[R] Z i.1)).comp
        (piSubtypeZeroExtend p Z) = LinearMap.id := by
  ext x i
  simp [piSubtypeZeroExtend, i.2]

/-- Extend an ordered family by zero on tuples that are not strictly increasing. -/
noncomputable def orderedCoefficientCechZeroExtendLinearMap
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    Ordered.CoefficientCechTerms.orderedCoefficientCechTerm ρ M U n →ₗ[R]
      (∀ i : Fin (n + 1) → ι, Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i) :=
  piSubtypeZeroExtend (fun i => StrictMono i)
    (fun i => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i)

theorem coefficientCechPiToOrderedLinearMap_comp_zeroExtend
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechPiToOrderedLinearMap ρ M U n).comp
      (orderedCoefficientCechZeroExtendLinearMap ρ M U n) = LinearMap.id := by
  exact piSubtypeRestriction_comp_zeroExtend (fun i => StrictMono i)
    (fun i => Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i)

theorem coefficientCechToOrderedF_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :
    FormalProjection.coefficientCechToOrderedF ρ M U n ≫
        Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
          Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j.1) i =
      Pi.π (fun j : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i.1 := by
  change (Pi.lift fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Pi.π (fun k : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n k) j.1 ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf ρ M).map (𝟙 _).op) ≫ _ = _
  simp

theorem orderedCoefficientCechObjectIsoPi_hom_comp_proj
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :
    (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi ρ M U n).hom ≫
        ModuleCat.ofHom
          (LinearMap.proj i : Ordered.CoefficientCechTerms.orderedCoefficientCechTerm ρ M U n →ₗ[
            R] Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i.1) =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j.1) i := by
  change (ModuleCat.piIsoPi (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j.1)).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = _
  exact ModuleCat.piIsoPi_hom_ker_subtype _ i

theorem coefficientCechXIsoPi_inv_comp_proj
    {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    (Intrinsic.CoefficientCechComplex.coefficientCechXIsoPi ρ M U n).inv ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) i =
      ModuleCat.ofHom
        (LinearMap.proj i :
          (∀ j : Fin (n + 1) → ι, Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n j) →ₗ[
            R] Ordered.CoefficientCechTerms.coefficientCechFactor ρ M U n i) := by
  exact ModuleCat.piIsoPi_inv_kernel_ι _ i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionCoordinates
