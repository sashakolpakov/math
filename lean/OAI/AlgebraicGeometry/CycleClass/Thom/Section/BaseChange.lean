import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupportRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseChange.Constructions.Class

noncomputable section

/-! The canonical section classes are compatible with restricting the
actual algebraic base and the original section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupportRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B C : V.carrier.Opens) (hCB : C ≤ B) [Nonempty B] [Nonempty C]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (U : Opens V.analyticSpace)
  (hUB : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hUC : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C)))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "sC" => Scheme.Hom.appTop (Scheme.homOfLE V.carrier hCB) s
local notation "FB" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "FC" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D C sC
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "DC" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val
local notation "u" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage DC U
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB s
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC sC

omit hUB [Nonempty B] [Nonempty C] in
include hUC in
theorem sectionBaseChange_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    {x : U | V.analyticUnderlying x.val ∈ FC}ᶜ {x : U | V.analyticUnderlying x.val ∈ FB}ᶜ :=
  fun _ hx hy => hx ((ClosedSupportRestriction.Constructions.sectionClosedSupport_restrict D B C hCB s U hUC).symm ▸ hy)

omit hUB [Nonempty B] [Nonempty C] in
theorem sectionBaseChange_injective (n : ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (sectionBaseChange_mapsTo D B C hCB s U hUC) n) := by
  rw [Supported.Transport.Constructions.Class.identityMap_eq_supportCast (TopCat.of U)
    (congrArg Set.compl (ClosedSupportRestriction.Constructions.sectionClosedSupport_restrict D B C hCB s U hUC).symm)
    (sectionBaseChange_mapsTo D B C hCB s U hUC) n]
  exact (ConcreteCategory.bijective_of_isIso _).injective

theorem sectionCupClass_base_restrict :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (sectionBaseChange_mapsTo D B C hCB s U hUC) (2 * q) (Cup.Constructions.Class.sectionCupClass D B s U hUB) =
      Cup.Constructions.Class.sectionCupClass D C sC U hUC := by
  let k : Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C ⟶ Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B := Thom.Scheme.SectionEvaluation.Constructions.openRestriction V.toOver hCB
  have hk : k ≫ Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B = Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C := Thom.Scheme.SectionEvaluation.Constructions.openRestriction_inclusion V.toOver hCB
  let hf : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range u)ᶜ := fun _ hx => hx
  let hg := BaseSectionChange.Constructions.baseSectionChange_mapsTo (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) k hk U hUB hUC s
  have hraw := ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction u v u w (𝟙 (TopCat.of U)) hf hg
    (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC U)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC U)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C) sC)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C) sC)) (Geometric.DimensionCycles.dimensionCodimension V D.val) 1
    (Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB s)
  have ha : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hf
      (2 * Geometric.DimensionCycles.dimensionCodimension V D.val) (Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U) = Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U :=
    ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range u)ᶜ (2 * Geometric.DimensionCycles.dimensionCodimension V D.val)) (Normalization.BaseImage.Constructions.Class.baseImageCycleClass DC U)
  have hb := BaseSectionChange.Constructions.baseSectionClass_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) k hk U hUB hUC s
  have hclasses := congrArg₂ (ImageIntersectionCup.Constructions.imageIntersectionCup u w (Normalization.GraphSectionCup.Constructions.baseImage_openComplement DC U)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C) sC)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C) sC)) (Geometric.DimensionCycles.dimensionCodimension V D.val) 1) ha hb
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) (𝟙 (TopCat.of U))
    (sectionBaseChange_mapsTo D B C hCB s U hUC) (Cup.Constructions.Class.cupSupport_mapsTo D B s U hUB) (2 * q)
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) (𝟙 (TopCat.of U))
    (Cup.Constructions.Class.cupSupport_mapsTo D C sC U hUC) (ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo u v u w (𝟙 (TopCat.of U)) hf hg) (2 * q)
  exact (ConcreteCategory.congr_hom (h₁.trans h₂.symm) _).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (Cup.Constructions.Class.cupSupport_mapsTo D C sC U hUC) (2 * q)) (hraw.trans hclasses))

variable [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C)]
  (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (hsC : Affine.SectionFunction.Constructions.parentSectionFunction D C ((V.carrier.homOfLE hCB).appTop s) ≠ 0)

omit hUB [Nonempty B] [Nonempty C] in
theorem sectionPrincipalClass_base_restrict :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (sectionBaseChange_mapsTo D B C hCB s U hUC) (2 * q) (Principal.Constructions.Class.sectionPrincipalClass D B s hs U) =
    Principal.Constructions.Class.sectionPrincipalClass D C sC hsC U := by
  have hc : Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs =
      Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D C sC) hsC := by
    congr 1
    exact (BaseRestriction.Constructions.parentSectionFunction_restrict D B C hCB s).symm
  have ht := Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U
    {x : U | V.analyticUnderlying x.val ∈ FB} {x : U | V.analyticUnderlying x.val ∈ FC}
    (ClosedSupportRestriction.Constructions.sectionClosedSupport_restrict D B C hCB s U hUC).symm q
    (Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs)
  have he := congrArg (fun c : Geometric.DimensionCycles.RationalDimensionCycle V q =>
    Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ FC} q
      (Open.SupportedLift.Constructions.restrictCycle V U {x : U | V.analyticUnderlying x.val ∈ FC} q c)) hc
  exact (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (sectionBaseChange_mapsTo D B C hCB s U hUC) (2 * q)) (Principal.Constructions.Class.sectionPrincipalClass_eq_local D B s hs U)).trans
    (ht.trans (he.trans (Principal.Constructions.Class.sectionPrincipalClass_eq_local D C sC hsC U).symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseChange.Constructions.Class
