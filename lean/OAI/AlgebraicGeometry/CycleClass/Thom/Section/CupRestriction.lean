import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionRestriction

/-! # Cup Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions

noncomputable section

/-! The actual cycle-section cups in the fixed algebraic support form a
compatible family under restriction of the ambient analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionRestriction.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U P : Opens V.analyticSpace) (hPU : P ≤ U)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hP : (P : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "DC" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "i" => CategoryTheory.Functor.map (Opens.toTopCat (TopCat.of V.analyticSpace)) (homOfLE hPU)
local notation "u" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage DC U
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage DC P
local notation "z" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j P hP s
local notation "hf" => OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction.Constructions.Class.baseImage_restriction_mapsTo DC U P hPU
local notation "hg" => OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionRestriction.Constructions.Class.baseSection_restriction_mapsTo j U P hPU hU hP s

 theorem sectionCupClass_restrict :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ (2 * q)).map (homOfLE hPU).op
      (Cup.Constructions.Class.sectionCupClass D B s U hU) = Cup.Constructions.Class.sectionCupClass D B s P hP := by
  let raw := ImageIntersectionCup.Constructions.imageIntersectionCup u v (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC U)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
    (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s)
  have hraw := ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction u v w z i hf hg (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC U)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC P)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j P hP) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
    (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s)
  have hclasses := congrArg₂
    (ImageIntersectionCup.Constructions.imageIntersectionCup w z (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC P)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j P hP) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
        (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)) (Geometric.DimensionCycles.dimensionCodimension V D.val) 1)
    (BaseImageRestriction.Constructions.Class.baseImageCycleClass_restrict DC U P hPU) (BaseSectionRestriction.Constructions.Class.baseSectionClass_restrict j U P hPU hU hP s)
  have hraw' := hraw.trans hclasses
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) i (𝟙 (TopCat.of U))
    (A := {x : P | V.analyticUnderlying x.val ∈ F}ᶜ) (B := {x : U | V.analyticUnderlying x.val ∈ F}ᶜ)
    (C := (Set.range u ∩ Set.range v)ᶜ) (fun _ hx => hx) (Cup.Constructions.Class.cupSupport_mapsTo D B s U hU) (2 * q)
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P)) i
    (Cup.Constructions.Class.cupSupport_mapsTo D B s P hP) (ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo u v w z i hf hg) (2 * q)
  exact (ConcreteCategory.congr_hom (h₁.trans h₂.symm) raw).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P))
      (Cup.Constructions.Class.cupSupport_mapsTo D B s P hP) (2 * q)) hraw')

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions
