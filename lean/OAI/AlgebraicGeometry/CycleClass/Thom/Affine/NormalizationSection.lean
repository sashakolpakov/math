import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionSupported
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionCommonBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrincipalCoefficients
import OAI.AlgebraicGeometry.CycleClass.Thom.BoundedAffineNormalizationGraph

/-! # Normalization Section -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationSection.Constructions.Class

noncomputable section

/-! The supported section formula on the actual affine normalization
source. Fiber coverage and all divisor good-open conditions follow from
the actual base open and the constructed global exceptional boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionCommonBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionSupported.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrincipalCoefficients.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)
  [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left] [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left]

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "X" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B
local notation "Y" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B
local notation "a" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB
local notation "g" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val

local instance : LocallyOfFiniteType (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).hom := by
  rw [← (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).w]
  infer_instance
local instance : IsLocallyNoetherian (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left := LocallyOfFiniteType.isLocallyNoetherian (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).hom
local instance : AlgebraicGeometry.IsNoetherian (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := inferInstance
local instance : Nonempty (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) := ⟨⟨genericPoint (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, Opens.mem_top _⟩⟩

variable (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (hsn : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.germToFunctionField ⊤ ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s) ≠ 0)

local notation "r" => Scheme.germToFunctionField (Over.left (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B)) ⊤ (Scheme.Hom.appTop (Over.Hom.left (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B)) s)
local notation "t" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions.originalFunction V D.val a r
local notation "ht" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions.originalFunction_ne_zero V D.val a r hsn

variable (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hgood : (U : Set V.analyticSpace) ⊆ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val
    (Normalization.OpenFunctionField.Constructions.originalFunction V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)
      ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.germToFunctionField ⊤ ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s)))
    (Normalization.OpenFunctionField.Constructions.originalFunction_ne_zero V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) _ hsn))

local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage P U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s)

variable (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (SchemeGraph.Constructions.globalGraphSchemeMap (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) f).left]
  (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) y) ∈ U →
    SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

include hf hK hb hgood in
theorem affine_cycle_sectionCup_eq_normalizedPrincipalClass :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V D.val + 1)
      (Open.SupportedLift.Constructions.restrictCycle V U S (Geometric.DimensionCycles.dimensionCodimension V D.val + 1) (Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val t ht)) := by
  let : Smooth (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).hom := Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_smooth D B hB
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := (SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf).isEmbedding.metrizableSpace
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).isEmbedding.metrizableSpace
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d)) := (SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d).isEmbedding.metrizableSpace
  have hsource : ∀ C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V D.val + 1),
      (∃ x : U, x.val ∈ Set.range C.analyticInclusion) →
      ∀ y : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val).left,
        (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val).left y = IntersectionGeometry.supportPoint C.val → y ∈ Set.range (a).left := by
    intro C hC
    apply NormalizationAffine.PrincipalCoefficients.Constructions.affineSource_fiber_cover D B hB
    apply Cycle.MeetingOpen.Constructions.supportPoint_mem_of_analytic_meets V C B U _ hC
    intro x hx
    exact (Set.ext_iff.mp (NormalizationAffine.OpenRange.Constructions.baseInclusion_analytic_range B) x).mp (hUJ hx)
  exact Normalization.SectionSupported.Constructions.cycle_sectionCup_eq_normalizedPrincipalClass V D.val a g j (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth_ambient D B hB)
    d f hf U hUJ (NormalizationAffine.OpenRange.Constructions.affine_source_cover D B hB U hUJ) s hsn
    (fun z => hgood.trans (Normalization.SectionCommonBoundary.Constructions.commonOpen_subset_sectionDivisor V D.val a ((g).left.appTop s) hsn z)) K hK hb hsource

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationSection.Constructions.Class
