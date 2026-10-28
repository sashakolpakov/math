/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactorNaturality

/-! # Pushforward Objects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardObjects

noncomputable section

/- Adapted for HilbertConstruction with explicit coefficient rings and the existing coefficient section comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- The ordered Cech object of an inverse-image cover agrees with the ordered Cech object of
the pushforward. -/
noncomputable def orderedCoefficientCechObjectPushforwardIso
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    Ordered.CoefficientCechTerms.orderedCoefficientCechObject (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n ≅
      Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap ((Scheme.Modules.pushforward f).obj M) U n :=
  Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n ≪≫
    LinearEquiv.toModuleIso
      (LinearEquiv.piCongrRight fun i : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).toLinearEquiv) ≪≫
    (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi coefficientMap ((Scheme.Modules.pushforward f).obj M) U n).symm

@[reassoc]
theorem orderedCoefficientCechObjectPushforwardIso_hom_π
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ)
    (i : Ordered.SectionCechIndices.OrderedCechIndex ι n) :
    (orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n).hom ≫
        Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n j.1) i =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
          Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun a ↦ f ⁻¹ᵁ U a) n j.1) i ≫
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).hom := by
  let A : Ordered.SectionCechIndices.OrderedCechIndex ι n → ModuleCat R :=
    fun j => Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun a ↦ f ⁻¹ᵁ U a) n j.1
  let B : Ordered.SectionCechIndices.OrderedCechIndex ι n → ModuleCat R :=
    fun j => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n j.1
  let ePi : ModuleCat.of R (∀ j, A j) ≅
      ModuleCat.of R (∀ j, B j) :=
    LinearEquiv.toModuleIso
      (LinearEquiv.piCongrRight fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n j.1).toLinearEquiv)
  change ((ModuleCat.piIsoPi A ≪≫ ePi ≪≫
      (ModuleCat.piIsoPi B).symm).hom ≫ Pi.π B i) =
    Pi.π A i ≫ (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).hom
  have hPi : ePi.hom ≫
        ModuleCat.ofHom (LinearMap.proj i : (∀ j, B j) →ₗ[R] B i) =
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[R] A i) ≫
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).hom := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  calc
    _ = (ModuleCat.piIsoPi A).hom ≫ ePi.hom ≫
        (ModuleCat.piIsoPi B).inv ≫ Pi.π B i := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rfl
    _ = (ModuleCat.piIsoPi A).hom ≫ ePi.hom ≫
        ModuleCat.ofHom (LinearMap.proj i : (∀ j, B j) →ₗ[R] B i) := by
      rw [ModuleCat.piIsoPi_inv_kernel_ι]
    _ = (ModuleCat.piIsoPi A).hom ≫
        (ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[R] A i) ≫
          (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).hom) := by
      rw [hPi]
    _ = ((ModuleCat.piIsoPi A).hom ≫
          ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[R] A i)) ≫
        (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n i.1).hom := by
      rw [Category.assoc]
    _ = _ := by rw [ModuleCat.piIsoPi_hom_ker_subtype]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardObjects
