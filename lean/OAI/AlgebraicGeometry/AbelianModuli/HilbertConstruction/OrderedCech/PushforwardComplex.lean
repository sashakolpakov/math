/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardCofaces

/-! # Pushforward Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardComplex

noncomputable section

/- Adapted for HilbertConstruction with explicit coefficient rings and the existing coefficient section comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedCoefficientCechObjectPushforwardIso_differential_naturality
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n).hom ≫
        Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap ((Scheme.Modules.pushforward f).obj M) U n =
      Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n ≫
        (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U (n + 1)).hom := by
  simp only [Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (PushforwardCofaces.orderedCoefficientCechObjectPushforwardIso_naturality f coefficientMap M U n k)

/-- Pushforward identifies the ordered base-linear Cech complex on a cover with the complex on
its inverse-image cover. -/
noncomputable def orderedCoefficientCechComplexPushforwardIso
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) :
    Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) ≅
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap ((Scheme.Modules.pushforward f).obj M) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d, Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
      exact orderedCoefficientCechObjectPushforwardIso_differential_naturality
        f coefficientMap M U i)

@[simp]
theorem orderedCoefficientCechComplexPushforwardIso_hom_f
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    (orderedCoefficientCechComplexPushforwardIso f coefficientMap M U).hom.f n =
      (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n).hom :=
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardComplex
