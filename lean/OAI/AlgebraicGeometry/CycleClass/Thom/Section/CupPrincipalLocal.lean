import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationSection
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport

/-! # Cup Principal Local -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalLocal.Constructions

noncomputable section

/-! On a bounded affine normalization neighborhood avoiding the genuine
exceptional boundary, the two canonical classes in the same algebraic
support agree. All rational functions come from the original section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.Nonzero OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationSection.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)
  [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left] [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hgood : (U : Set V.analyticSpace) ⊆ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : Nonempty (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) :=
  ⟨⟨genericPoint (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, Opens.mem_top _⟩⟩

variable (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) f).left]
  (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) y) ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage P U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s)
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "c" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs

include hf hK hb hgood in
theorem sectionCupClass_eq_principal_bounded :
    Cup.Constructions.Class.sectionCupClass D B s U hUJ = Principal.Constructions.Class.sectionPrincipalClass D B s hs U := by
  have hsn := Affine.SectionFunction.Constructions.Nonzero.sourceSection_germ_ne_zero D B hB s hs
  have hgood' : (U : Set V.analyticSpace) ⊆ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val
      (Normalization.OpenFunctionField.Constructions.originalFunction V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)
        ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.germToFunctionField ⊤ ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s)))
      (Normalization.OpenFunctionField.Constructions.originalFunction_ne_zero V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) _ hsn) := by
    simpa only [Affine.SectionFunction.Constructions.originalFunction_eq_parentSectionFunction] using hgood
  have hlocal := Affine.NormalizationSection.Constructions.Class.affine_cycle_sectionCup_eq_normalizedPrincipalClass D B hB s hsn U hUJ hgood' d f hf K hK hb
  have h : ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
        (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
      (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S q (Open.SupportedLift.Constructions.restrictCycle V U S q c) := by
    simpa only [Affine.SectionFunction.Constructions.originalFunction_eq_parentSectionFunction] using hlocal
  exact (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (Cup.Constructions.Class.cupSupport_mapsTo D B s U hUJ) (2 * q)) h).trans
    ((Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U S {x : U | V.analyticUnderlying x.val ∈ F}
      (Cup.Constructions.Class.cupSupport_eq_closedSupport D B s U hUJ) q c).trans
      (Principal.Constructions.Class.sectionPrincipalClass_eq_local D B s hs U).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalLocal.Constructions
