/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison

/-! # Ordered Base Cech Pushforward -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-!
# Ordered Cech complexes and pushforward

This file identifies the ordered base-linear Cech complex of a module on the inverse-image
cover with the ordered Cech complex of its pushforward. The comparison uses that inverse image
preserves the finite intersections occurring in each Cech factor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

/-- Sections of a module and sections of its pushforward agree as modules over the base. -/
noncomputable def baseModulePresheafPushforwardAppIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    (V : Y.Opens) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).obj (Opposite.op (f ⁻¹ᵁ V)) ≅
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).obj (Opposite.op V) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext x
  let x' : Γ(M, f ⁻¹ᵁ V) := x
  change
    (f.app V).hom
          ((π.appLE (⊤ : S.Opens) V le_top).hom r) • x' =
      ((f ≫ π).appLE (⊤ : S.Opens) (f ⁻¹ᵁ V) le_top).hom r • x'
  have h := Scheme.Hom.appLE_comp_appLE f π
    (⊤ : S.Opens) V (f ⁻¹ᵁ V) le_top le_rfl
  have hr := ConcreteCategory.congr_hom h r
  have hr' :
      (f.app V).hom ((π.appLE (⊤ : S.Opens) V le_top).hom r) =
        ((f ≫ π).appLE (⊤ : S.Opens) (f ⁻¹ᵁ V) le_top).hom r := by
    rw [f.app_eq_appLE]
    simpa only [CommRingCat.comp_apply] using hr
  exact congrArg (fun q => q • x') hr'

/-- Each Cech factor on the inverse-image cover agrees with the corresponding factor of the
pushforward. -/
noncomputable def baseCechFactorPushforwardIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n i ≅
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n i :=
  (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).mapIso
      (eqToIso ((Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U n i)).op ≪≫
    baseModulePresheafPushforwardAppIso f π M
      (∏ᶜ fun k : Fin (n + 1) => U (i k))

theorem baseCechFactorPushforwardIso_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map
          (((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op ≫
        (baseCechFactorPushforwardIso f π M U (n + 1) i).hom =
      (baseCechFactorPushforwardIso f π M U n
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).map
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
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map sourceFace.op =
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map sourceRestriction :=
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).congr_map (Subsingleton.elim _ _)
  have hTargetMap :
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op =
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).map
          targetRestrictionAmbient :=
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).congr_map
      (Subsingleton.elim _ _)
  have hMiddle :
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map sourceRestriction ≫
          (baseCechFactorPushforwardIso f π M U (n + 1) i).hom =
        (baseCechFactorPushforwardIso f π M U n
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
          (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).map
            targetRestrictionAmbient := by
    apply ModuleCat.hom_ext
    ext x
    let highTransport :=
      (eqToHom ((Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U (n + 1) i)).op
    let lowTransport :=
      (eqToHom ((Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U n j)).op
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
    _ = (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map sourceRestriction ≫
          (baseCechFactorPushforwardIso f π M U (n + 1) i).hom :=
      congrArg
        (fun q => q ≫ (baseCechFactorPushforwardIso f π M U (n + 1) i).hom)
        hSourceMap
    _ = _ := hMiddle
    _ = _ := congrArg
      (fun q => (baseCechFactorPushforwardIso f π M U n
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫ q)
      hTargetMap.symm

/-- The ordered Cech object of an inverse-image cover agrees with the ordered Cech object of
the pushforward. -/
noncomputable def orderedBaseCechObjectPushforwardIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n ≅
      OrderedBaseCech.Scheme.Modules.orderedBaseCechObject π ((pushforward f).obj M) U n :=
  OrderedBaseCech.Scheme.Modules.orderedBaseCechObjectIsoPi (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n ≪≫
    LinearEquiv.toModuleIso
      (LinearEquiv.piCongrRight fun i : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
        (baseCechFactorPushforwardIso f π M U n i.1).toLinearEquiv) ≪≫
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechObjectIsoPi π ((pushforward f).obj M) U n).symm

@[reassoc]
theorem orderedBaseCechObjectPushforwardIso_hom_π
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ)
    (i : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n) :
    (orderedBaseCechObjectPushforwardIso f π M U n).hom ≫
        Pi.π (fun j : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n j.1) i =
      Pi.π (fun j : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun a ↦ f ⁻¹ᵁ U a) n j.1) i ≫
        (baseCechFactorPushforwardIso f π M U n i.1).hom := by
  let A : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n → ModuleCat Γ(S, (⊤ : S.Opens)) :=
    fun j => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun a ↦ f ⁻¹ᵁ U a) n j.1
  let B : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n → ModuleCat Γ(S, (⊤ : S.Opens)) :=
    fun j => Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n j.1
  let ePi : ModuleCat.of Γ(S, (⊤ : S.Opens)) (∀ j, A j) ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens)) (∀ j, B j) :=
    LinearEquiv.toModuleIso
      (LinearEquiv.piCongrRight fun j : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
        (baseCechFactorPushforwardIso f π M U n j.1).toLinearEquiv)
  change ((ModuleCat.piIsoPi A ≪≫ ePi ≪≫
      (ModuleCat.piIsoPi B).symm).hom ≫ Pi.π B i) =
    Pi.π A i ≫ (baseCechFactorPushforwardIso f π M U n i.1).hom
  have hPi : ePi.hom ≫
        ModuleCat.ofHom (LinearMap.proj i : (∀ j, B j) →ₗ[Γ(S, ⊤)] B i) =
      ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[Γ(S, ⊤)] A i) ≫
        (baseCechFactorPushforwardIso f π M U n i.1).hom := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  calc
    _ = (ModuleCat.piIsoPi A).hom ≫ ePi.hom ≫
        (ModuleCat.piIsoPi B).inv ≫ Pi.π B i := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rfl
    _ = (ModuleCat.piIsoPi A).hom ≫ ePi.hom ≫
        ModuleCat.ofHom (LinearMap.proj i : (∀ j, B j) →ₗ[Γ(S, ⊤)] B i) := by
      rw [ModuleCat.piIsoPi_inv_kernel_ι]
    _ = (ModuleCat.piIsoPi A).hom ≫
        (ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[Γ(S, ⊤)] A i) ≫
          (baseCechFactorPushforwardIso f π M U n i.1).hom) := by
      rw [hPi]
    _ = ((ModuleCat.piIsoPi A).hom ≫
          ModuleCat.ofHom (LinearMap.proj i : (∀ j, A j) →ₗ[Γ(S, ⊤)] A i)) ≫
        (baseCechFactorPushforwardIso f π M U n i.1).hom := by
      rw [Category.assoc]
    _ = _ := by rw [ModuleCat.piIsoPi_hom_ker_subtype]

private theorem orderedBaseCechObjectPushforwardIso_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ)
    (k : Fin (n + 2)) :
    (orderedBaseCechObjectPushforwardIso f π M U n).hom ≫
        OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π ((pushforward f).obj M) U n k =
      OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k ≫
        (orderedBaseCechObjectPushforwardIso f π M U (n + 1)).hom := by
  let sourceLow := OrderedBaseCech.Scheme.Modules.orderedBaseCechObject (f ≫ π) M
    (fun j ↦ f ⁻¹ᵁ U j) n
  let sourceHigh := OrderedBaseCech.Scheme.Modules.orderedBaseCechObject (f ≫ π) M
    (fun j ↦ f ⁻¹ᵁ U j) (n + 1)
  let targetLow := OrderedBaseCech.Scheme.Modules.orderedBaseCechObject π ((pushforward f).obj M) U n
  let targetHigh := OrderedBaseCech.Scheme.Modules.orderedBaseCechObject π ((pushforward f).obj M) U (n + 1)
  let eLow : sourceLow ≅ targetLow :=
    orderedBaseCechObjectPushforwardIso f π M U n
  let eHigh : sourceHigh ≅ targetHigh :=
    orderedBaseCechObjectPushforwardIso f π M U (n + 1)
  let sourceCoface : sourceLow ⟶ sourceHigh :=
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k
  let targetCoface : targetLow ⟶ targetHigh :=
    OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π ((pushforward f).obj M) U n k
  let targetPi := OrderedBaseCech.Scheme.Modules.orderedBaseCechObjectIsoPi π ((pushforward f).obj M) U (n + 1)
  change eLow.hom ≫ targetCoface = sourceCoface ≫ eHigh.hom
  apply (cancel_mono targetPi.hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext a
  let sourceLowProj : sourceLow ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 :=
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n b.1) (a.delete k)
  let sourceHighProj : sourceHigh ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 :=
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (n + 1) =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) b.1) a
  let targetLowProj : targetLow ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n (a.delete k).1 :=
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n b.1) (a.delete k)
  let targetHighProj : targetHigh ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U (n + 1) a.1 :=
    Pi.π (fun b : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (n + 1) =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U (n + 1) b.1) a
  let sourceMap :
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 :=
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ π) M).map
      (((FormalCoproduct.mk _ (fun j ↦ f ⁻¹ᵁ U j)).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a.1).op
  let targetMap :
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n (a.delete k).1 ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U (n + 1) a.1 :=
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π ((pushforward f).obj M)).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ a.1).op
  let factorLow :
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n (a.delete k).1 ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U n (a.delete k).1 :=
    (baseCechFactorPushforwardIso f π M U n (a.delete k).1).hom
  let factorHigh :
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) (n + 1) a.1 ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π ((pushforward f).obj M) U (n + 1) a.1 :=
    (baseCechFactorPushforwardIso f π M U (n + 1) a.1).hom
  have hTargetCoface :
      targetCoface ≫ targetHighProj = targetLowProj ≫ targetMap := by
    exact OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π π ((pushforward f).obj M) U n k a
  have hSourceCoface :
      sourceCoface ≫ sourceHighProj = sourceLowProj ≫ sourceMap := by
    exact OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π
      (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n k a
  have hLowIso :
      eLow.hom ≫ targetLowProj = sourceLowProj ≫ factorLow := by
    exact orderedBaseCechObjectPushforwardIso_hom_π
      f π M U n (a.delete k)
  have hHighIso :
      eHigh.hom ≫ targetHighProj = sourceHighProj ≫ factorHigh := by
    exact orderedBaseCechObjectPushforwardIso_hom_π f π M U (n + 1) a
  have hFactor :
      sourceMap ≫ factorHigh = factorLow ≫ targetMap := by
    exact baseCechFactorPushforwardIso_naturality f π M U n k a.1
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
    rw [OrderedBaseCechComparison.Scheme.Modules.orderedBaseCechObjectIsoPi_hom_comp_proj]
    exact hProjected
  change
    (ModuleCat.ofHom (LinearMap.proj a)).hom
        (targetPi.hom.hom (targetCoface.hom (eLow.hom.hom x))) =
      (ModuleCat.ofHom (LinearMap.proj a)).hom
        (targetPi.hom.hom (eHigh.hom.hom (sourceCoface.hom x)))
  exact ConcreteCategory.congr_hom hConcrete x

private theorem orderedBaseCechObjectPushforwardIso_differential_naturality
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    (orderedBaseCechObjectPushforwardIso f π M U n).hom ≫
        OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential π ((pushforward f).obj M) U n =
      OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) n ≫
        (orderedBaseCechObjectPushforwardIso f π M U (n + 1)).hom := by
  simp only [OrderedBaseCech.Scheme.Modules.orderedBaseCechDifferential, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    (orderedBaseCechObjectPushforwardIso_naturality f π M U n k)

/-- Pushforward identifies the ordered base-linear Cech complex on a cover with the complex on
its inverse-image cover. -/
noncomputable def orderedBaseCechComplexPushforwardIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (f ≫ π) M (fun j ↦ f ⁻¹ᵁ U j) ≅
      OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π ((pushforward f).obj M) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ orderedBaseCechObjectPushforwardIso f π M U n) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d, OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_d]
      exact orderedBaseCechObjectPushforwardIso_differential_naturality
        f π M U i)

@[simp]
theorem orderedBaseCechComplexPushforwardIso_hom_f
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    (orderedBaseCechComplexPushforwardIso f π M U).hom.f n =
      (orderedBaseCechObjectPushforwardIso f π M U n).hom :=
  rfl

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules
