import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceOver
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductCycleSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Product Chart -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart.BundleCycles

/-! Genuine open product charts of a scheme morphism. The record contains
only schemes, maps, a limiting product cone, and native geometric properties. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

structure SchemeOpenProductChart {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : E ⟶ X) (z : E.left) where
  base : Over Foundations.Scheme.ProjectiveSpace.complexBase
  total : Over Foundations.Scheme.ProjectiveSpace.complexBase
  fiber : Over Foundations.Scheme.ProjectiveSpace.complexBase
  baseMap : base ⟶ X
  totalMap : total ⟶ E
  fiberProjection : total ⟶ fiber
  baseProjection : total ⟶ base
  baseOpen : IsOpenImmersion baseMap.left
  totalOpen : IsOpenImmersion totalMap.left
  mem : z ∈ Set.range totalMap.left
  square : totalMap ≫ f = baseProjection ≫ baseMap
  product : IsLimit (BinaryFan.mk fiberProjection baseProjection)
  fiberIntegral : IsIntegral fiber.left
  fiberSmooth : Smooth fiber.hom
  fiberMetrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints fiber)

namespace SchemeOpenProductChart

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} {f : E ⟶ X} {z : E.left} (c : SchemeOpenProductChart f z)

instance baseMap_open : IsOpenImmersion c.baseMap.left := c.baseOpen
instance totalMap_open : IsOpenImmersion c.totalMap.left := c.totalOpen
instance fiber_integral : IsIntegral c.fiber.left := c.fiberIntegral
instance fiber_smooth : Smooth c.fiber.hom := c.fiberSmooth
instance fiber_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.fiber) := c.fiberMetrizable

instance total_nonempty : Nonempty c.total.left := by
  obtain ⟨t, _⟩ := c.mem
  exact ⟨t⟩

instance base_nonempty : Nonempty c.base.left :=
  Nonempty.map c.baseProjection.left (total_nonempty c)

instance base_integral [IsIntegral X.left] : IsIntegral c.base.left :=
  isIntegral_of_isOpenImmersion c.baseMap.left

instance total_integral [IsIntegral E.left] : IsIntegral c.total.left :=
  isIntegral_of_isOpenImmersion c.totalMap.left

instance base_smooth [Smooth X.hom] : Smooth c.base.hom := by
  have h : Smooth (c.baseMap.left ≫ X.hom) := smooth_comp c.baseMap.left X.hom
  exact c.baseMap.w ▸ h

instance total_smooth [Smooth E.hom] : Smooth c.total.hom := by
  have h : Smooth (c.totalMap.left ≫ E.hom) := smooth_comp c.totalMap.left E.hom
  exact c.totalMap.w ▸ h

instance base_noetherian [AlgebraicGeometry.IsNoetherian X.left] : AlgebraicGeometry.IsNoetherian c.base.left :=
  ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian c.baseMap.left

instance total_noetherian [AlgebraicGeometry.IsNoetherian E.left] : AlgebraicGeometry.IsNoetherian c.total.left :=
  ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian c.totalMap.left

instance base_metrizable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.base) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion c.baseMap).isEmbedding.metrizableSpace

instance total_metrizable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints c.total) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion c.totalMap).isEmbedding.metrizableSpace

theorem point_mem (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E) (hq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q = z) :
    q ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.totalMap) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  exact hq.symm ▸ c.mem

end SchemeOpenProductChart

end AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart.BundleCycles

namespace AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart.BundleCycles.SchemeOpenProductChart
open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
section

/-! Every open product chart through an inverse-image support point
meets both actual restricted supports. Their dimensions are inherited
from the genuine open immersions. -/

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} {f : E ⟶ X} {z : E.left} (c : SchemeOpenProductChart f z)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left)) (hz : z ∈ (C : Set E.left))

include hz in
theorem totalSupport_nonempty : Nonempty (SupportRestriction.BundleCycles.openSupportPullback c.totalMap.left C) := by
  obtain ⟨t, ht⟩ := c.mem
  apply (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff c.totalMap.left C).mpr
  refine ⟨t, ?_⟩
  change c.totalMap.left t ∈ (C : Set E.left)
  rw [ht]
  exact hz

include hC hz in
theorem baseSupport_nonempty : Nonempty (SupportRestriction.BundleCycles.openSupportPullback c.baseMap.left B) := by
  obtain ⟨t, ht⟩ := c.mem
  apply (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff c.baseMap.left B).mpr
  refine ⟨c.baseProjection.left t, ?_⟩
  have he : f.left (c.totalMap.left t) = c.baseMap.left (c.baseProjection.left t) :=
    congrArg (fun k : c.total ⟶ X => k.left t) c.square
  have hb : f.left z ∈ (B : Set X.left) := (Set.ext_iff.mp hC z).mp hz
  change c.baseMap.left (c.baseProjection.left t) ∈ (B : Set X.left)
  rw [← he, ht]
  exact hb

end

/-! Codimension is preserved by an actual open product chart meeting
the support. This follows from the proved dimensions of products and
open immersions, without a constant-rank hypothesis. -/

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [IsIntegral X.left] [Smooth X.hom]
    {f : E ⟶ X} {z : E.left} (c : SchemeOpenProductChart f z)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left)) (hz : z ∈ (C : Set E.left))

include c hC hz in
omit [Smooth E.hom] in
theorem inverseImage_codimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom := by
  let := c.totalSupport_nonempty C hz
  let := c.baseSupport_nonempty B C hC hz
  let A := SupportRestriction.BundleCycles.openRestrictedSupport c.baseMap.left B
  let D := SupportRestriction.BundleCycles.openRestrictedSupport c.totalMap.left C
  have hA := SupportRestriction.BundleCycles.openRestrictedSupport_coe c.baseMap.left B
  have hD := SupportRestriction.BundleCycles.openRestrictedSupport_coe c.totalMap.left C
  have hDP := ProductCycleSquare.BundleCycles.openProductSupport_preimage f c.baseMap c.totalMap c.baseProjection c.square B C A D hC hA hD
  have he : D = Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport c.fiber c.base A c.total c.fiberProjection c.baseProjection c.product :=
    SetLike.coe_injective (hDP.trans
      (Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport_coe c.fiber c.base A c.total c.fiberProjection c.baseProjection c.product).symm)
  have ha := SupportOver.BundleCycles.openRestrictedSupportOver_codimension c.baseMap B p hp
  have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D c.total.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension c.total.hom := by
    rw [he]
    exact Projection.SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension c.fiber c.base A c.total
      c.fiberProjection c.baseProjection c.product p ha
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportRestriction.BundleCycles.openRestrictedSupport c.totalMap.left C) c.total.hom + p =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension c.total.hom at hd
  rw [SupportOver.BundleCycles.openRestrictedSupportOver_dimension, SupportOver.BundleCycles.openImmersionOver_dimension c.totalMap] at hd
  exact hd

end AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart.BundleCycles.SchemeOpenProductChart

end

end OAI
