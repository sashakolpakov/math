import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentation
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation

/-! # Vector One Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorOneStep.Constructions

noncomputable section

/-! The one-section base case for the actual finite-cycle vector
class is its original principal-step sum, with the same support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (p : ℕ) (B : V.carrier.Opens) [Nonempty B] (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hr : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0)

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU r
local notation "hv" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) r)
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) r)
local notation "s" => (fun _ : Fin 1 => r)
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class.vectorIntersectionSupport V B U hU u 1 s

include hc in
theorem cycleVectorClass_one :
    Vector.Constructions.Class.cycleVectorClassAt V B U hU u p 1 (p + 1) rfl s hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1)
        (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hr)) := by
  have hT : Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage j U hU 1 s) = Set.range v := BaseVectorNormal.Constructions.Class.vectorZeroImage_one j U hU s
  have hg : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector j U hU 1 s) (Set.range v)ᶜ ({0}ᶜ) := by
    rw [BaseVectorNormal.Constructions.Class.baseSectionVector_one]
    exact BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r
  apply VectorPresentation.Constructions.present_injective V B U hU u 1 s (Set.range u) (Set.range v) rfl hT (2 * (p + 1))
  rw [VectorPresentation.Constructions.present_cycleVectorClass V B U hU u 1 s (Set.range u) (Set.range v) rfl hT p (p + 1) rfl
      hu hu hv (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v) hg c,
    VectorPresentation.Constructions.present_cycleClass V B U hU u 1 s (Set.range u) (Set.range v) rfl hT (p + 1)]
  have hn := ConcreteCategory.congr_hom
    (ThomOpenRestriction.Constructions.pairMap_congr (BaseVectorNormal.Constructions.Class.baseSectionVector_one j U hU s) hg (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU r) 2)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  rw [hn]
  have h := Finite.SectionCup.Constructions.cycle_sectionEquationCup_eq_step V p B r U hU u hu c hc hne hr
  rwa [Finite.SectionEuler.Constructions.cycleSectionStep_eq_sum] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorOneStep.Constructions
