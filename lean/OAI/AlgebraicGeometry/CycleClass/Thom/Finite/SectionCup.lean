import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass
import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange

/-! # Section Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup.Constructions

noncomputable section

/-! The finite section-step class identity expressed through the
actual section equation and the literal output support complement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

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

theorem cycle_sectionEquationCup_eq_step :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range u)ᶜ (Set.range v)ᶜ Sᶜ hu hv (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v)
      (2 * p) 2 (2 * (p + 1)) (Nat.mul_add 2 p 1).symm
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU s)
        (BaseSectionChange.Constructions.Equation.baseSectionEquation_mapsTo j U hU s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (CycleSectionClass.Constructions.cycleSectionStep V p B s U u c hc hne hs)) := by
  have h := CycleSectionClass.Constructions.cycle_sectionCup_eq_step V p B s U hU u hu c hc hne hs
  rw [BaseSectionChange.Constructions.Equation.baseSectionClass_eq_equation] at h
  exact (EvenIntersectionAssociativity.Constructions.SupportedCupTargets.imageIntersectionCup_eq_cupTo u v hu hv p 1 _ _).symm.trans h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionCup.Constructions
