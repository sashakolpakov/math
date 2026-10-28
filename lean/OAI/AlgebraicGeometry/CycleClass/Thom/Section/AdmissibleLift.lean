import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup

/-! # Admissible Lift -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions.StepClass

/-! The canonical finite principal-divisor step commutes with the actual
supported cup by a regular section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.PrincipalCommonSupport OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions.Linearity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens) [Nonempty B]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "I" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.AdmissibleSupport V p B s U u
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s
local notation "hv" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
local notation "S" => Set.range u ∩ Set.range v

theorem sectionCup_eq_supportedStep (c : I →₀ ℚ) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Step.Constructions.parentSupportedCycleMap V p B s U u c)) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Step.Constructions.stepSupportedCycleMap V p B s U hU u c) := by
  suffices h : ((ImageIntersectionCup.Constructions.Linearity.imageIntersectionCupLinear u v hu hv p 1).flip (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s)).comp
        ((Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p).comp (Step.Constructions.parentSupportedCycleMap V p B s U u)) =
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1)).comp (Step.Constructions.stepSupportedCycleMap V p B s U hU u) from
    LinearMap.congr_fun h c
  apply Finsupp.lhom_ext
  intro D r
  change ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Step.Constructions.parentSupportedCycleMap V p B s U u (Finsupp.single D r)))
      (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Step.Constructions.stepSupportedCycleMap V p B s U hU u (Finsupp.single D r))
  rw [Step.Constructions.parentSupportedCycleMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Open.SupportedLift.Constructions.Map.relativeClassMap_single, ImageIntersectionCup.Constructions.Linearity.imageIntersectionCup_smul_left,
    Step.Constructions.stepSupportedCycleMap, Finsupp.linearCombination_single, map_smul]
  apply congrArg (fun a => r • a)
  let := D.sourceNonempty
  exact Step.Constructions.PrincipalCommonSupport.supportedGenerator_sectionCup_eq_principalStep D.support.val B s D.sectionNonzero U hU u hu D.support.property

theorem sectionCup_eq_stepCycle (c : I →₀ ℚ) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Step.Constructions.parentSupportedCycleMap V p B s U u c)) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (Step.Constructions.stepCycleMap V p B s U u c)) := by
  exact (sectionCup_eq_supportedStep V p B s U hU u hu c).trans
    (Open.SupportedLift.Constructions.relativeClassMap_eq_restrict_of_local_coefficients V U S (p + 1)
      (Step.Constructions.stepSupportedCycleMap V p B s U hU u c) (Step.Constructions.stepCycleMap V p B s U u c)
      (fun C _ => congrArg (fun e => e C) (Step.Constructions.forget_stepSupportedCycleMap V p B s U hU u c)))

end AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions.StepClass

namespace AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions

/-! Every finite original cycle supported in the prescribed image and
nonzero under the actual section admits a canonical admissible lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions.StepClass OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens)
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  {L : Type} (u : L → U) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

def admissibleOfCoefficient (D : {D : Geometric.DimensionCycles.DimensionCycleSupport V p // c D ≠ 0}) : Step.Constructions.AdmissibleSupport V p B s U u where
  support := ⟨D.val, hc D.val D.property⟩
  sourceNonempty := hne D.val D.property
  sectionNonzero := hs D.val D.property

def admissibleCycle : Step.Constructions.AdmissibleSupport V p B s U u →₀ ℚ :=
  Finsupp.mapDomain (admissibleOfCoefficient V p B s U u c hc hne hs)
    (c.subtypeDomain (fun D => c D ≠ 0))

theorem forget_parent_admissibleCycle :
    Open.SupportedLift.Constructions.Map.forgetCycle V U (Set.range u) p
      (Step.Constructions.parentSupportedCycleMap V p B s U u (admissibleCycle V p B s U u c hc hne hs)) = c := by
  change Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (fun D : Step.Constructions.AdmissibleSupport V p B s U u => D.support)
    (Finsupp.mapDomain (admissibleOfCoefficient V p B s U u c hc hne hs)
      (c.subtypeDomain (fun D => c D ≠ 0)))) = c
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  change Finsupp.mapDomain Subtype.val (c.subtypeDomain (fun D => c D ≠ 0)) = c
  exact (Finsupp.embDomain_eq_mapDomain
    (Function.Embedding.subtype (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p => c D ≠ 0)) _).symm.trans
    ((Finsupp.extendDomain_eq_embDomain_subtype _).symm.trans
      (Finsupp.extendDomain_subtypeDomain c (fun D hD => Finsupp.mem_support_iff.mp hD)))

theorem parentClass_eq_restrict :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p
      (Step.Constructions.parentSupportedCycleMap V p B s U u (admissibleCycle V p B s U u c hc hne hs)) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c) :=
  Open.SupportedLift.Constructions.relativeClassMap_eq_restrict_of_local_coefficients V U (Set.range u) p _ c
    (fun D _ => congrArg (fun e => e D) (forget_parent_admissibleCycle V p B s U u c hc hne hs))

end AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions

end

end OAI
