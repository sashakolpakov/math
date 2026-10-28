import OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift

/-! # Cycle Section Class -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions

noncomputable section

/-! The actual finite cycle class commutes with its genuine section
divisor step, in the original cycle grading and intersection support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions.StepClass OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens) [Nonempty B]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s
local notation "hv" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
local notation "S" => Set.range u ∩ Set.range v

def cycleSectionStep : Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) :=
  Section.Step.Constructions.stepCycleMap V p B s U u (Section.AdmissibleLift.Constructions.admissibleCycle V p B s U u c hc hne hs)

theorem cycleSectionStep_supported (D : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hD : cycleSectionStep V p B s U u c hc hne hs D ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S := by
  apply Open.SupportedLift.Constructions.forgetCycle_supported V U S (p + 1)
    (Section.Step.Constructions.stepSupportedCycleMap V p B s U hU u (Section.AdmissibleLift.Constructions.admissibleCycle V p B s U u c hc hne hs)) D
  rw [Section.Step.Constructions.forget_stepSupportedCycleMap]
  exact hD

theorem cycle_sectionCup_eq_step :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c)) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (cycleSectionStep V p B s U u c hc hne hs)) := by
  have h := congrArg (fun a => ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1 a (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s))
    (Section.AdmissibleLift.Constructions.parentClass_eq_restrict V p B s U u c hc hne hs)
  exact h.symm.trans (Section.AdmissibleLift.Constructions.StepClass.sectionCup_eq_stepCycle V p B s U hU u hu (Section.AdmissibleLift.Constructions.admissibleCycle V p B s U u c hc hne hs))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions
