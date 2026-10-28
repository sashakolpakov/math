import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Good

/-! # Finite Parent -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.FiniteParent.BundleCycles

noncomputable section

/-! The actual smooth normalization has generic degree one and its finite image is precisely the restriction of the original closed support to the normalization ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left)

local instance normalizationFiniteParentSourceNonempty :
    Nonempty ((AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W) :=
  inferInstanceAs (Nonempty (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSmoothNormalization_genericDegree :
    (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left.residueDegree
      (genericPoint (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left) = 1 := by
  have hr := CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_residueDegree (AmbientMap.BundleCycles.schemeNormalizationToAmbient X W) (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)
  change (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left.residueDegree
    (genericPoint (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left) =
      (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W).residueDegree
        (genericPoint (CycleClass.Thom.Normalization.Scheme.Constructions.normalization (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) at hr
  rw [CycleClass.Thom.ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion] at hr
  exact hr.trans (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap_generic_residueDegree (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSmoothNormalization_nativeCodimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom + p =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Ambient.BundleCycles.schemeNormalizationAmbientOver X W).hom := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    Topology.BundleCycles.schemeSmoothNormalization_dimension, Ambient.BundleCycles.schemeNormalizationAmbient_dimension]
  exact hp

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSmoothNormalization_finite_range :
    Set.range (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left =
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left ⁻¹' (W : Set X.left) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W]
    exact ⟨CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) z.val,
      (Good.BundleCycles.schemeNormalizationFullAmbientMap_apply X W z).symm⟩
  · intro hy
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι W] at hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨z, hz⟩ := CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap_surjective (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) t
    have he : CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) z) = y.val :=
      (congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W) hz).trans ht
    have hzo : z ∈ (AmbientMap.BundleCycles.schemeNormalizationToAmbient X W).left ⁻¹ᵁ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W := by
      change CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.Normalization.Scheme.Constructions.normalizationMap (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) z) ∈ AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W
      exact he.symm ▸ y.property
    refine ⟨⟨z, hzo⟩, ?_⟩
    apply Subtype.ext
    exact (Good.BundleCycles.schemeNormalizationFullAmbientMap_apply X W ⟨z, hzo⟩).trans he

instance schemeNormalizationAmbientSupport_nonempty : Nonempty
    (Open.SupportRestriction.BundleCycles.openSupportPullback (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left W) := by
  apply (Open.SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff _ _).mpr
  rw [← schemeSmoothNormalization_finite_range]
  exact Set.range_nonempty _

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizationFiniteParent_image :
    CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)) =
      Open.SupportRestriction.BundleCycles.openRestrictedSupport (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left W := by
  apply SetLike.coe_injective
  rw [CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_eq_image, Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe]
  change (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left '' closure {genericPoint (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left} = _
  rw [(genericPoint_spec (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left).def, Set.image_univ]
  exact schemeSmoothNormalization_finite_range X W

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.FiniteParent.BundleCycles
