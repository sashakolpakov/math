import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionZeroSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage

/-! # Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class

noncomputable section

/-! The actual parent-cycle and section cup, expressed in the fixed
algebraic closed support used for local detection and boundary removal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionZeroSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage P U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s)
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1

theorem cupSupport_eq_closedSupport : S = {x : U | V.analyticUnderlying x.val ∈ F} :=
  (Affine.SectionZeroSupport.Constructions.sectionClosedSupport_analytic_range P B s U hUJ).symm

theorem cupSupport_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    {x : U | V.analyticUnderlying x.val ∈ F}ᶜ Sᶜ :=
  fun _ hx hy => hx ((cupSupport_eq_closedSupport D B s U hUJ) ▸ hy)

def sectionCupClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) ((V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ) U) (2 * q) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (cupSupport_mapsTo D B s U hUJ) (2 * q)
    (ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
        (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
      (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class
