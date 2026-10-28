import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedEnlargement

/-! # Step -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.PrincipalCommonSupport

/-! One genuine principal-divisor step is compatible with the supported
cup in any common parent support containing the original cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageEnlargement.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedEnlargement.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ)
  (hD : (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s
local notation "hv" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
local notation "S₀" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage D U) ∩ Set.range v
local notation "S₁" => Set.range u ∩ Set.range v

include hD in
omit [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] in
theorem intersectionSupport_le : S₀ ⊆ S₁ := by
  intro x hx
  exact ⟨hD ((Set.ext_iff.mp (Normalization.BaseImage.Constructions.Class.baseImage_range D U) x).mp hx.1), hx.2⟩

include hD in
theorem principalStep_supported_common (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hC : CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range C.analyticInclusion ⊆ S₁ :=
  (CupPrincipalGeneral.Constructions.Step.principalStep_supported D B s hs U hU C hC).trans (intersectionSupport_le D B s U hU u hD)

theorem supportedGenerator_sectionCup_eq_principalStep :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1 (Open.SupportedLift.Constructions.Map.relativeGenerator V U (Set.range u) p ⟨D, hD⟩) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S₁ (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S₁ (p + 1) (CupPrincipalGeneral.Constructions.Step.principalStep D B s hs)) := by
  let hf := BaseImageEnlargement.Constructions.Class.parentImage_mapsTo D U u hD
  let hg : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range v)ᶜ (Set.range v)ᶜ := fun _ hx => hx
  have hr := ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction (Normalization.BaseImage.Constructions.Class.baseImage D U) v u v (𝟙 (TopCat.of U)) hf hg
    (Normalization.GraphSectionCup.Constructions.baseImage_openComplement D U) hv hu hv p 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s)
  have hb : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hg 2 (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
      IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s :=
    ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range v)ᶜ 2)
      (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s)
  have hc := congrArg₂ (ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p 1)
    (BaseImageEnlargement.Constructions.Class.parentClass_enlarge_eq_generator D U u hD) hb
  have he := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (A := S₁ᶜ) (B := S₀ᶜ) (fun _ hx hy => hx (intersectionSupport_le D B s U hU u hD hy)) (2 * (p + 1)))
    (CupPrincipalGeneral.Constructions.Step.cycle_sectionCup_eq_principalStep D B s hs U hU)
  exact (hr.trans hc).symm.trans (he.trans
    (Open.SupportedEnlargement.Constructions.restrictCycle_class_enlarge V U S₀ S₁ (intersectionSupport_le D B s U hU u hD) (p + 1)
      (CupPrincipalGeneral.Constructions.Step.principalStep D B s hs) (CupPrincipalGeneral.Constructions.Step.principalStep_supported D B s hs U hU)))

end AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.PrincipalCommonSupport

namespace AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions

/-! A finite cycle of actual parent supports on which a section is
nonzero has a canonical principal-divisor step. The admissibility data
contain only source nonemptiness and nonvanishing of the actual section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.PrincipalCommonSupport OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure AdmissibleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens)
    (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace) {L : Type} (u : L → U) where
  support : Open.SupportedLift.Constructions.Map.SupportedSupport V U (Set.range u) p
  sourceNonempty : Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V support.val.val).left ⁻¹ᵁ B)
  sectionNonzero : letI := sourceNonempty
    Affine.SectionFunction.Constructions.parentSectionFunction support.val B s ≠ 0

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens) [Nonempty B]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "I" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions.AdmissibleSupport V p B s U u
local notation "S" => Set.range u ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU s)

def stepCycle (D : I) : Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) := by
  let := D.sourceNonempty
  exact CupPrincipalGeneral.Constructions.Step.principalStep D.support.val B s D.sectionNonzero

include hU in
theorem stepCycle_supported (D : I) (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hC : stepCycle V p B s U u D C ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range C.analyticInclusion ⊆ S := by
  let := D.sourceNonempty
  exact PrincipalCommonSupport.principalStep_supported_common D.support.val B s D.sectionNonzero U hU u D.support.property C hC

def supportedStep (D : I) : Open.SupportedLift.Constructions.Map.SupportedCycle V U S (p + 1) := Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (stepCycle V p B s U u D)

theorem forget_supportedStep (D : I) :
    Open.SupportedLift.Constructions.Map.forgetCycle V U S (p + 1) (supportedStep V p B s U hU u D) = stepCycle V p B s U u D :=
  Open.SupportedLift.Constructions.forget_restrictCycle V U S (p + 1) (stepCycle V p B s U u D) (stepCycle_supported V p B s U hU u D)

def parentSupportedCycleMap : (I →₀ ℚ) →ₗ[ℚ] Open.SupportedLift.Constructions.Map.SupportedCycle V U (Set.range u) p :=
  Finsupp.lmapDomain ℚ ℚ (fun D : I => D.support)

def stepSupportedCycleMap : (I →₀ ℚ) →ₗ[ℚ] Open.SupportedLift.Constructions.Map.SupportedCycle V U S (p + 1) :=
  Finsupp.linearCombination ℚ (supportedStep V p B s U hU u)

def stepCycleMap : (I →₀ ℚ) →ₗ[ℚ] Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) :=
  Finsupp.linearCombination ℚ (stepCycle V p B s U u)

theorem forget_stepSupportedCycleMap (c : I →₀ ℚ) :
    Open.SupportedLift.Constructions.Map.forgetCycle V U S (p + 1) (stepSupportedCycleMap V p B s U hU u c) = stepCycleMap V p B s U u c := by
  suffices h : (Open.SupportedLift.Constructions.Map.forgetCycle V U S (p + 1)).comp (stepSupportedCycleMap V p B s U hU u) =
      stepCycleMap V p B s U u from LinearMap.congr_fun h c
  apply Finsupp.lhom_ext
  intro D r
  change Open.SupportedLift.Constructions.Map.forgetCycle V U S (p + 1) (stepSupportedCycleMap V p B s U hU u (Finsupp.single D r)) =
    stepCycleMap V p B s U u (Finsupp.single D r)
  rw [stepSupportedCycleMap, stepCycleMap, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, map_smul, forget_supportedStep]

end AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions

end

end OAI
