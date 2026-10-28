/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardObjects

/-! # Pushforward Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardCofaces

noncomputable section

/- Adapted for HilbertConstruction with explicit coefficient rings and the existing coefficient section comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedCoefficientCechObjectPushforwardIso_naturality
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ)
    (k : Fin (n + 2)) :
    (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n).hom ≫
        Ordered.CoefficientCechTerms.orderedCoefficientCechCoface coefficientMap ((Scheme.Modules.pushforward f).obj M) U n k =
      Ordered.CoefficientCechTerms.orderedCoefficientCechCoface (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n k ≫
        (PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U (n + 1)).hom := by
  let sourceLow := Ordered.CoefficientCechTerms.orderedCoefficientCechObject (f.appTop.hom.comp coefficientMap) M
    (fun j ↦ f ⁻¹ᵁ U j) n
  let sourceHigh := Ordered.CoefficientCechTerms.orderedCoefficientCechObject (f.appTop.hom.comp coefficientMap) M
    (fun j ↦ f ⁻¹ᵁ U j) (n + 1)
  let targetLow := Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap ((Scheme.Modules.pushforward f).obj M) U n
  let targetHigh := Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1)
  let eLow : sourceLow ≅ targetLow :=
    PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U n
  let eHigh : sourceHigh ≅ targetHigh :=
    PushforwardObjects.orderedCoefficientCechObjectPushforwardIso f coefficientMap M U (n + 1)
  let sourceCoface : sourceLow ⟶ sourceHigh :=
    Ordered.CoefficientCechTerms.orderedCoefficientCechCoface (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n k
  let targetCoface : targetLow ⟶ targetHigh :=
    Ordered.CoefficientCechTerms.orderedCoefficientCechCoface coefficientMap ((Scheme.Modules.pushforward f).obj M) U n k
  let targetPi := Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1)
  change eLow.hom ≫ targetCoface = sourceCoface ≫ eHigh.hom
  apply (cancel_mono targetPi.hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext a
  let sourceLowProj : sourceLow ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 :=
    Pi.π (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n b.1) (a.delete k)
  let sourceHighProj : sourceHigh ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 :=
    Pi.π (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) b.1) a
  let targetLowProj : targetLow ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n (a.delete k).1 :=
    Pi.π (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n b.1) (a.delete k)
  let targetHighProj : targetHigh ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1) a.1 :=
    Pi.π (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1) b.1) a
  let sourceMap :
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).map
      (((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a.1).op
  let targetMap :
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n (a.delete k).1 ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1) a.1 :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a.1).op
  let factorLow :
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n (a.delete k).1 :=
    (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U n (a.delete k).1).hom
  let factorHigh :
      Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U (n + 1) a.1 :=
    (CoefficientCech.PushforwardFactors.coefficientCechFactorPushforwardIso f coefficientMap M U (n + 1) a.1).hom
  have hTargetCoface :
      targetCoface ≫ targetHighProj = targetLowProj ≫ targetMap := by
    exact Ordered.CoefficientCechTerms.orderedCoefficientCechCoface_comp_π coefficientMap ((Scheme.Modules.pushforward f).obj M) U n k a
  have hSourceCoface :
      sourceCoface ≫ sourceHighProj = sourceLowProj ≫ sourceMap := by
    exact Ordered.CoefficientCechTerms.orderedCoefficientCechCoface_comp_π
      (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n k a
  have hLowIso :
      eLow.hom ≫ targetLowProj = sourceLowProj ≫ factorLow := by
    exact PushforwardObjects.orderedCoefficientCechObjectPushforwardIso_hom_π
      f coefficientMap M U n (a.delete k)
  have hHighIso :
      eHigh.hom ≫ targetHighProj = sourceHighProj ≫ factorHigh := by
    exact PushforwardObjects.orderedCoefficientCechObjectPushforwardIso_hom_π f coefficientMap M U (n + 1) a
  have hFactor :
      sourceMap ≫ factorHigh = factorLow ≫ targetMap := by
    exact CoefficientCech.PushforwardFactorNaturality.coefficientCechFactorPushforwardIso_naturality f coefficientMap M U n k a.1
  have hTargetPath :
      (eLow.hom ≫ targetCoface) ≫ targetHighProj =
        sourceLowProj ≫ (factorLow ≫ targetMap) := by
    rw [Category.assoc, hTargetCoface, ← Category.assoc, hLowIso,
      Category.assoc]
  have hSourcePath :
      (sourceCoface ≫ eHigh.hom) ≫ targetHighProj =
        sourceLowProj ≫ (sourceMap ≫ factorHigh) := by
    rw [Category.assoc, hHighIso, ← Category.assoc, hSourceCoface,
      Category.assoc]
  have hProjected :
      (eLow.hom ≫ targetCoface) ≫ targetHighProj =
        (sourceCoface ≫ eHigh.hom) ≫ targetHighProj := by
    rw [hTargetPath, hSourcePath, hFactor]
  have hConcrete :
      ((eLow.hom ≫ targetCoface) ≫ targetPi.hom) ≫
          ModuleCat.ofHom (LinearMap.proj a) =
        ((sourceCoface ≫ eHigh.hom) ≫ targetPi.hom) ≫
          ModuleCat.ofHom (LinearMap.proj a) := by
    simp only [Category.assoc]
    rw [ProjectionCoordinates.orderedCoefficientCechObjectIsoPi_hom_comp_proj]
    exact hProjected
  change
    (ModuleCat.ofHom (LinearMap.proj a)).hom
        (targetPi.hom.hom (targetCoface.hom (eLow.hom.hom x))) =
      (ModuleCat.ofHom (LinearMap.proj a)).hom
        (targetPi.hom.hom (eHigh.hom.hom (sourceCoface.hom x)))
  exact ConcreteCategory.congr_hom hConcrete x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardCofaces
