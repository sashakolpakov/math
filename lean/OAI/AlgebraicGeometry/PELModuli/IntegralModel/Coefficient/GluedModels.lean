import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms
import OAI.ArithmeticGeometry.Models.GluingFiniteness

/-! # Glued Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GluedModels.Coefficients

/-! Generalization of the proved GluedModels construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Constructing a model of a union from models of its two open pieces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

open OAI.ArithmeticGeometry.Models.GluingFiniteness.Constructions.Foundations

universe u

theorem open_gluing_has_model
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] [IsNoetherianRing R₀]
    {W X Y P : Over (Spec (CommRingCat.of K))}
    (f : W ⟶ X) (g : W ⟶ Y) (i : X ⟶ P) (j : Y ⟶ P)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] [CompactSpace W.left]
    (hP : IsPushout f.left g.left i.left j.left)
    (MX : Models.Coefficients.CoefficientModel R₀ K X) (MY : Models.Coefficients.CoefficientModel R₀ K Y) :
    Nonempty (Models.Coefficients.CoefficientModel R₀ K P) := by
  classical
  obtain ⟨sX, ⟨L⟩⟩ := OpenImmersionStages.Coefficients.open_immersion_has_stage f MX
  obtain ⟨sY, ⟨R⟩⟩ := OpenImmersionStages.Coefficients.open_immersion_has_stage g MY
  let s := sX ∪ sY
  let L₁ := L.enlarge (show sX ⊆ s from Finset.subset_union_left)
  let R₁ := R.enlarge (show sY ⊆ s from Finset.subset_union_right)
  obtain ⟨t, hst, e, he⟩ := Isomorphisms.Coefficients.isomorphism_between_models_descends
    L₁.source R₁.source L₁.sourceFP R₁.sourceFP L₁.pSource R₁.pSource
    L₁.sourceCartesian R₁.sourceCartesian (Iso.refl W)
  let L₂ := L₁.enlarge hst
  let R₂ := R₁.enlarge hst
  let e₂ : L₂.source ≅ R₂.source := e
  have he' : L₂.pSource ≫ e₂.hom.left = R₂.pSource := by
    exact he.trans (Category.id_comp _)
  let f₀ : L₂.source ⟶ L₂.target := L₂.inclusion
  let g₀ : L₂.source ⟶ R₂.target := e₂.hom ≫ R₂.inclusion
  let : IsOpenImmersion f₀.left := L₂.openInclusion
  let : IsOpenImmersion R₂.inclusion.left := R₂.openInclusion
  let : IsOpenImmersion e₂.hom.left := by
    change IsOpenImmersion ((Over.forget _).mapIso e₂).hom
    infer_instance
  let : IsOpenImmersion g₀.left := by
    change IsOpenImmersion (e₂.hom.left ≫ R₂.inclusion.left)
    infer_instance
  have hg : g.left ≫ R₂.pTarget = L₂.pSource ≫ g₀.left := by
    change g.left ≫ R₂.pTarget = L₂.pSource ≫ (e₂.hom.left ≫ R₂.inclusion.left)
    erw [← Category.assoc, he']
    exact R₂.compatibility.symm
  let P₀ := ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.openGluedOver f₀ g₀
  let b := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t
  have hG := ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.openGluedBaseChange_isPushout b f g f₀ g₀
    L₂.pSource L₂.pTarget R₂.pTarget
    L₂.sourceCartesian L₂.targetCartesian R₂.targetCartesian L₂.compatibility.symm hg
  let eP : ((Over.pullback b).obj P₀).left ≅ P.left :=
    hG.isoIsPushout X.left Y.left hP
  have heP : eP.hom ≫ P.hom = ((Over.pullback b).obj P₀).hom := by
    apply hG.hom_ext
    · rw [← Category.assoc, IsPushout.inl_isoIsPushout_hom]
      exact i.w.trans (ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.baseChangeChart_snd b (ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.openGluedInl f₀ g₀) L₂.pTarget
        L₂.targetCartesian.w).symm
    · rw [← Category.assoc, IsPushout.inr_isoIsPushout_hom]
      exact j.w.trans (ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.baseChangeChart_snd b (ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations.openGluedInr f₀ g₀) R₂.pTarget
        R₂.targetCartesian.w).symm
  let : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t) := Finiteness.Coefficients.coefficientBase_locallyNoetherian R₀ K t
  exact ⟨{
    coefficients := t
    model := P₀
    finitePresentation := ArithmeticGeometry.Models.GluingFiniteness.Constructions.Foundations.openGluedOver_finitePresentation f₀ g₀ L₂.targetFP R₂.targetFP
    genericIso := Over.isoMk eP heP }⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GluedModels.Coefficients
