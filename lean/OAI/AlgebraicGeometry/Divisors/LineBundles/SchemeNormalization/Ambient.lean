import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Topology
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver

/-! # Ambient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient.BundleCycles

noncomputable section

section

/-! The actual ambient complement of the normalization exceptional
locus is a smooth integral Noetherian scheme of the original dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (W : IrreducibleCloseds X.left)

abbrev schemeNormalizationAmbientOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)

instance schemeNormalizationAmbientOpen_nonempty : Nonempty (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W) := by
  let y : (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left := Classical.choice inferInstance
  exact ⟨(AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left y⟩

instance schemeNormalizationAmbientOver_integral : IsIntegral (schemeNormalizationAmbientOver X W).left :=
  inferInstanceAs (IsIntegral (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W).toScheme)

instance schemeNormalizationAmbientOver_smooth : Smooth (schemeNormalizationAmbientOver X W).hom :=
  smooth_comp (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W).ι X.hom

instance schemeNormalizationAmbientOver_noetherian : AlgebraicGeometry.IsNoetherian (schemeNormalizationAmbientOver X W).left :=
  @Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W).toScheme X.left inferInstance
    (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W).ι inferInstance

instance schemeNormalizationAmbientOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (schemeNormalizationAmbientOver X W)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W))).isEmbedding.metrizableSpace

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizationAmbient_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (schemeNormalizationAmbientOver X W).hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom :=
  Open.SupportOver.BundleCycles.openImmersionOver_dimension (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W))

end

/-! Algebraic open restriction agrees with the ordinary analytic
subspace restriction through the actual complex-point homeomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem schemeOpenBetti_isIso_of_subspace (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) (n : ℕ)
    (h : IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) n)) :
    IsIso (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U)) := by
  let e := TopCat.isoOfHomeo (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X U)))
    (Y := TopCat.of (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U)) (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph X U)
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  have he : e.hom ≫ j = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U) := by
    ext x
    rfl
  let : IsIso (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) j n) := h
  let : IsIso (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) e.hom n) := by
    change IsIso ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℚ ℚ) n).map e.hom.op)
    infer_instance
  change IsIso (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U)) n)
  rw [← he]
  have hc := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ) e.hom j n
  exact (congrArg IsIso hc).mpr inferInstance

theorem schemeNormalizationAmbientBetti_isIso
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (W : IrreducibleCloseds X.left) (d p : ℕ)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = d + 1)
    (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    IsIso (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p)
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W))) := by
  apply schemeOpenBetti_isIso_of_subspace
  apply CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedComplement_restriction_isIso
    X (Boundary.BundleCycles.schemeNormalizationExceptional X W) (p + 1) ?_ (p + p) (by omega)
  intro Z hZ
  have h := Boundary.BundleCycles.schemeNormalizationExceptional_dimension X W Z hZ
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.Ambient.BundleCycles
