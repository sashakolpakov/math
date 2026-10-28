import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedOpenClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedClassZero

/-! # Graded Absolute Open Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteOpenClass.BundleCycles

noncomputable section

/-! The canonical class commutes with actual open restriction on every
finite dimension-graded cycle, retaining or omitting each genuine support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (i : X ⟶ Y) [IsOpenImmersion i.left]
    (d p : ℕ) (hY : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeOpenGradedAbsolutePointClass (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i
      (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (irreducibleSetEquivPoints.symm (Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d x).val) p
        ((congrArg (fun k => k + p) (Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d x).property).trans hY)) =
    AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (irreducibleSetEquivPoints.symm x.val) p
      ((congrArg (fun k => k + p) x.property).trans (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hY)) := by
  have h := AbsoluteOpenPullback.BundleCycles.schemeAbsoluteCycleClass_openPullback i (irreducibleSetEquivPoints.symm (i.left x.val)) p
    ((congrArg (fun k => k + p) (Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d x).property).trans hY)
  exact h.trans (Finite.GradedClassZero.BundleCycles.schemeAbsoluteCycleClass_congrSupport (X := X) _ _ (Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure i.left x.val) p _ _)

theorem schemeGradedAbsoluteCycleClass_openRestriction :
    (GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hY)).comp (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d) =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i).hom.comp (GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d p hY) := by
  classical
  apply Finsupp.lhom_ext
  intro x a
  change GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hY)
      (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d (Finsupp.single x a)) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i (GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d p hY (Finsupp.single x a))
  by_cases hx : x.val ∈ Set.range i.left
  · obtain ⟨y, hy⟩ := hx
    have hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) X.hom = d := by
      have h := ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i.left Y.hom y
      rw [i.w, hy] at h
      exact h.symm.trans x.property
    let z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d := ⟨y, hdim⟩
    have he : x = Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d z := Subtype.ext hy.symm
    rw [he, Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction_single, GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, map_smul]
    exact congrArg (fun t => a • t) (schemeOpenGradedAbsolutePointClass i d p hY z).symm
  · rw [Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction_single_off i d x a hx, map_zero, GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, map_smul]
    have he : i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val : Set Y.left) = ∅ :=
      SchemeCycle.EmptyPullback.BundleCycles.openSupport_preimage_empty_of_generic_not_mem i _ (by simpa only [OrderIso.apply_symm_apply] using hx)
    rw [SchemeCycle.EmptyPullback.BundleCycles.schemeAbsoluteCycleClass_pullback_empty i _ p _ he, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteOpenClass.BundleCycles
