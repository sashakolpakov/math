import OAI.ArithmeticGeometry.Models.OpenImmersion
import OAI.ArithmeticGeometry.Models.BaseChange
import OAI.ArithmeticGeometry.Models.ModelFiniteness

/-! # Open Immersion Stages -/

namespace OAI.ArithmeticGeometry.Models.OpenImmersionStages.Constructions.Foundations

/-! Changing the coefficient ring of an open-immersion model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

variable {K : Type u} [Field K]

structure OpenImmersionAtBase (s : Finset K)
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X) where
  source : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)
  target : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)
  sourceFP : Scheme.Constructions.Foundations.FinitePresentationMorphism source.hom
  targetFP : Scheme.Constructions.Foundations.FinitePresentationMorphism target.hom
  inclusion : source ⟶ target
  openInclusion : IsOpenImmersion inclusion.left
  pSource : W.left ⟶ source.left
  pTarget : X.left ⟶ target.left
  sourceCartesian : IsPullback pSource W.hom source.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  targetCartesian : IsPullback pTarget X.hom target.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  compatibility : pSource ≫ inclusion.left = f.left ≫ pTarget

noncomputable def OpenImmersionAtBase.enlarge {s t : Finset K} (h : s ⊆ t)
    {W X : Over (Spec (CommRingCat.of K))} {f : W ⟶ X} (M : OpenImmersionAtBase s f) :
    OpenImmersionAtBase t f := by
  let B := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  let : IsOpenImmersion M.inclusion.left := M.openInclusion
  have hopen : IsOpenImmersion (B.map M.inclusion).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (FoundationsPullback.Constructions.pullback_over_map_isPullback _ M.inclusion).flip inferInstance
  exact {
    source := B.obj M.source
    target := B.obj M.target
    sourceFP := ModelFiniteness.Constructions.Foundations.baseChange_finitePresentation _ _ M.sourceFP
    targetFP := ModelFiniteness.Constructions.Foundations.baseChange_finitePresentation _ _ M.targetFP
    inclusion := B.map M.inclusion
    openInclusion := hopen
    pSource := ModelMorphisms.Constructions.Foundations.genericModelLift M.source M.pSource M.sourceCartesian.w h
    pTarget := ModelMorphisms.Constructions.Foundations.genericModelLift M.target M.pTarget M.targetCartesian.w h
    sourceCartesian := ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian M.source M.pSource M.sourceCartesian h
    targetCartesian := ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian M.target M.pTarget M.targetCartesian h
    compatibility := BaseChange.Constructions.Foundations.genericModelLift_map M.source M.target M.pSource M.pTarget
      M.sourceCartesian.w M.targetCartesian.w f M.inclusion M.compatibility h }

theorem open_immersion_has_stage
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left] (M : Foundations.Constructions.CoefficientModel K X) :
    ∃ s, Nonempty (OpenImmersionAtBase s f) := by
  obtain ⟨L⟩ := OpenImmersion.Constructions.Foundations.open_immersion_has_model f M
  exact ⟨L.ambient.coefficients, ⟨{
    source := L.source
    target := L.ambient.model
    sourceFP := L.sourceFP
    targetFP := L.ambient.finitePresentation
    inclusion := L.inclusion
    openInclusion := L.openInclusion
    pSource := L.specialization
    pTarget := L.ambient.specialization
    sourceCartesian := L.cartesian
    targetCartesian := L.ambient.cartesian
    compatibility := L.compatibility.symm }⟩⟩

end OAI.ArithmeticGeometry.Models.OpenImmersionStages.Constructions.Foundations
