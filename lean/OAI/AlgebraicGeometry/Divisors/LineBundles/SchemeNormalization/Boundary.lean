import OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupportDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity

/-! # Boundary -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Boundary.BundleCycles

noncomputable section

/-! For an integral closed support in a general smooth scheme, the
image of the normalization's singular locus has two additional support
codimensions. Its removal preserves the principal-cycle cohomology degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.NestedSupportDimension.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (W : IrreducibleCloseds X.left)

def schemeNormalizationExceptional : Closeds X.left :=
  ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W '' CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSingularImage (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom),
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.isClosedMap _
      (CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open.normalizationSingularImage (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom)).isClosed⟩

theorem schemeNormalizationExceptional_dimension (Z : IrreducibleCloseds X.left)
    (hZ : (Z : Set X.left) ⊆ schemeNormalizationExceptional X W) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + 2 ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom := by
  have hz : irreducibleSetEquivPoints Z ∈ (Z : Set X.left) := by
    have h := subset_closure (Set.mem_singleton (irreducibleSetEquivPoints Z))
    change irreducibleSetEquivPoints Z ∈
      (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z) : Set X.left) at h
    simpa only [OrderIso.symm_apply_apply] using h
  obtain ⟨x, hx, he⟩ := hZ hz
  obtain ⟨y, hy, hey⟩ := hx
  have hheight : 1 < coheight x := hey ▸
    CycleClass.Thom.Normalization.SmoothLocus.Constructions.normalization_singular_image_coheight_gt_one (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.hom) y hy
  have hd := CycleClass.Thom.NestedSupportDimension.Constructions.supportPoint_dimension_add_two_le X.hom W x hheight
  rw [he, OrderIso.symm_apply_apply] at hd
  exact hd

theorem schemeNormalizationExceptional_codimension [IsIntegral X.left] (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (Z : IrreducibleCloseds X.left) (hZ : (Z : Set X.left) ⊆ schemeNormalizationExceptional X W) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + (p + 2) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  have h := schemeNormalizationExceptional_dimension X W Z hZ
  omega

theorem schemeNormalizationExceptional_restriction_isIso [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (schemeNormalizationExceptional X W : Set X.left))ᶜ
      (2 * (p + 1))) :=
  CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedComplement_restriction_isIso X
    (schemeNormalizationExceptional X W) (p + 2) (schemeNormalizationExceptional_codimension X W p hp)
    (2 * (p + 1)) (by omega)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Boundary.BundleCycles
