/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactors

/-! # Pushforward Factor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactorNaturality

noncomputable section

/- Adapted for HilbertConstruction with explicit coefficient rings and the existing coefficient section comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem coefficientCechFactorPushforwardIso_naturality
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map
          (((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op ≫
        (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U (n + 1) i).hom =
      (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
  let δ := (SimplexCategory.δ k).toOrderHom.toFun
  let j : Fin (n + 1) → ι := i ∘ δ
  let sourceFace :=
    ((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower δ).φ i
  let targetFace := ((FormalCoproduct.mk _ U).mapPower δ).φ i
  let sourceHigh : X.Opens :=
    ∏ᶜ fun a : Fin (n + 2) => f ⁻¹ᵁ U (i a)
  let sourceLow : X.Opens :=
    ∏ᶜ fun a : Fin (n + 1) => f ⁻¹ᵁ U (j a)
  let targetHigh : Y.Opens := ∏ᶜ fun a : Fin (n + 2) => U (i a)
  let targetLow : Y.Opens := ∏ᶜ fun a : Fin (n + 1) => U (j a)
  have hSource : sourceHigh ≤ sourceLow := leOfHom sourceFace
  have hTarget : targetHigh ≤ targetLow := leOfHom targetFace
  let sourceRestriction : Opposite.op sourceLow ⟶ Opposite.op sourceHigh :=
    (homOfLE hSource).op
  let targetRestrictionAmbient : Opposite.op targetLow ⟶ Opposite.op targetHigh :=
    (homOfLE hTarget).op
  have hSourceMap :
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map sourceFace.op =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map sourceRestriction :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).congr_map (Subsingleton.elim _ _)
  have hTargetMap :
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).map
          targetRestrictionAmbient :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).congr_map
      (Subsingleton.elim _ _)
  have hMiddle :
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map sourceRestriction ≫
          (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U (n + 1) i).hom =
        (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).map
            targetRestrictionAmbient := by
    apply ModuleCat.hom_ext
    ext x
    let highTransport :=
      (eqToHom (PushforwardFactors.preimageCechIntersection f U (n + 1) i)).op
    let lowTransport :=
      (eqToHom (PushforwardFactors.preimageCechIntersection f U n j)).op
    let targetRestriction :=
      (Opens.map f.base).op.map targetRestrictionAmbient
    let x' : Γ(M, sourceLow) := x
    change
      (M.presheaf.map highTransport).hom
          ((M.presheaf.map sourceRestriction).hom x') =
        (M.presheaf.map targetRestriction).hom
          ((M.presheaf.map lowTransport).hom x')
    have hComposite :
        M.presheaf.map sourceRestriction ≫ M.presheaf.map highTransport =
          M.presheaf.map lowTransport ≫ M.presheaf.map targetRestriction := by
      rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
      exact M.presheaf.congr_map (Subsingleton.elim _ _)
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom hComposite x'
  calc
    _ = (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map sourceRestriction ≫
          (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U (n + 1) i).hom :=
      congrArg
        (fun q => q ≫ (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U (n + 1) i).hom)
        hSourceMap
    _ = _ := hMiddle
    _ = _ := congrArg
      (fun q => (PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫ q)
      hTargetMap.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactorNaturality
