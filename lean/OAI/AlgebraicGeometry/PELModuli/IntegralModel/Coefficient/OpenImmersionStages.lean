import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Open Immersion Stages -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages.Coefficients

/-! Generalization of the proved OpenImmersionStages construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Changing the coefficient ring of an open-immersion model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K]

structure OpenImmersionAtBase (s : Finset K)
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X) where
  source : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)
  target : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)
  sourceFP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism source.hom
  targetFP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism target.hom
  inclusion : source ⟶ target
  openInclusion : IsOpenImmersion inclusion.left
  pSource : W.left ⟶ source.left
  pTarget : X.left ⟶ target.left
  sourceCartesian : IsPullback pSource W.hom source.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
  targetCartesian : IsPullback pTarget X.hom target.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
  compatibility : pSource ≫ inclusion.left = f.left ≫ pTarget

noncomputable def OpenImmersionAtBase.enlarge {s t : Finset K} (h : s ⊆ t)
    {W X : Over (Spec (CommRingCat.of K))} {f : W ⟶ X} (M : OpenImmersionAtBase (R₀ := R₀) s f) :
    OpenImmersionAtBase (R₀ := R₀) t f := by
  let B := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)
  let : IsOpenImmersion M.inclusion.left := M.openInclusion
  have hopen : IsOpenImmersion (B.map M.inclusion).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback _ M.inclusion).flip inferInstance
  exact {
    source := B.obj M.source
    target := B.obj M.target
    sourceFP := Finiteness.Coefficients.baseChange_finitePresentation _ _ M.sourceFP
    targetFP := Finiteness.Coefficients.baseChange_finitePresentation _ _ M.targetFP
    inclusion := B.map M.inclusion
    openInclusion := hopen
    pSource := Morphisms.Coefficients.genericModelLift M.source M.pSource M.sourceCartesian.w h
    pTarget := Morphisms.Coefficients.genericModelLift M.target M.pTarget M.targetCartesian.w h
    sourceCartesian := Morphisms.Coefficients.genericModelLift_cartesian M.source M.pSource M.sourceCartesian h
    targetCartesian := Morphisms.Coefficients.genericModelLift_cartesian M.target M.pTarget M.targetCartesian h
    compatibility := BaseChange.Coefficients.genericModelLift_map M.source M.target M.pSource M.pTarget
      M.sourceCartesian.w M.targetCartesian.w f M.inclusion M.compatibility h }

theorem open_immersion_has_stage
    {W X : Over (Spec (CommRingCat.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left] (M : Models.Coefficients.CoefficientModel R₀ K X) :
    ∃ s, Nonempty (OpenImmersionAtBase (R₀ := R₀) s f) := by
  obtain ⟨L⟩ := OpenImmersionModels.Coefficients.open_immersion_has_model f M
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

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages.Coefficients
