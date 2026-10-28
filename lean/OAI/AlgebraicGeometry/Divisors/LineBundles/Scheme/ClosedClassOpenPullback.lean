import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleOpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassPullbackGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedSupportedLift

/-! # Closed Class Open Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassOpenPullback.BundleCycles

noncomputable section

/-! Canonical common-support classes commute with actual open restriction of finite graded cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsOpenImmersion i.left] (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeClosedRelativeClassMap_openPullback (c : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle Y F d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (ClosedClassPullbackGenerator.BundleCycles.schemeClosedPullback_mapsTo i F) (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y F d p hd c) =
    OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d p
      (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hd) (ClosedCycleOpenRestriction.BundleCycles.schemeClosedCycleOpenRestriction i F d c) := by
  classical
  let L : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) Fᶜ (2 * p) →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F)ᶜ (2 * p) :=
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (ClosedClassPullbackGenerator.BundleCycles.schemeClosedPullback_mapsTo i F) (2 * p)).hom
  change L (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y F d p hd c) = _
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x r =>
    by_cases hx : x.val.val ∈ Set.range i.left
    · obtain ⟨y, hy⟩ := hx
      have hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) X.hom = d := by
        have h := ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i.left Y.hom y
        rw [i.w, hy] at h
        exact h.symm.trans x.val.property
      let y' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d := ⟨y, hdim⟩
      have he : Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d y' = x.val := Subtype.ext hy
      let z : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d :=
        ⟨y', ClosedCycleOpenRestriction.BundleCycles.schemeClosedOpenPoint_support i F d x y' he⟩
      have hz : Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d z.val = x.val := he
      let : Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i.left (irreducibleSetEquivPoints.symm x.val.val)) :=
        (Open.SupportGenericPoint.BundleCycles.openSupportPullback_nonempty_generic i.left _).mpr
          (by simpa only [OrderIso.apply_symm_apply] using (show x.val.val ∈ Set.range i.left from ⟨y, hy⟩))
      have hZ : (irreducibleSetEquivPoints.symm z.val.val : Set X.left) =
          i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val.val : Set Y.left) := by
        change (irreducibleSetEquivPoints.symm y : Set X.left) = _
        rw [← hy, ← Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe i.left, Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure]
      rw [ClosedCycleOpenRestriction.BundleCycles.schemeClosedCycleOpenRestriction_single i F d x z hz r,
        OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, map_smul]
      exact congrArg (fun a => r • a) (ClosedClassPullbackGenerator.BundleCycles.schemeClosedRelativeGenerator_pullback_support i F d p hd x z hZ)
    · rw [ClosedCycleOpenRestriction.BundleCycles.schemeClosedCycleOpenRestriction_single_off i F d x hx r,
        map_zero, OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, map_smul]
      let M : ModuleCat ℚ := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F)ᶜ (2 * p)
      have hzero : r • (0 : M) = 0 := smul_zero r
      exact (congrArg (fun a => r • a)
        (ClosedClassPullbackGenerator.BundleCycles.schemeClosedRelativeGenerator_pullback_empty i F d p hd x hx)).trans hzero

theorem schemeClosedRestrictedClass_openPullback (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ)
    (hc : ∀ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d, c z ≠ 0 →
      Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm z.val)) ⊆ F) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (ClosedClassPullbackGenerator.BundleCycles.schemeClosedPullback_mapsTo i F) (2 * p)
      (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y F d p hd (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y F d c)) =
    OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d p
      (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hd)
      (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d c)) := by
  rw [schemeClosedRelativeClassMap_openPullback, ClosedCycleOpenRestriction.BundleCycles.schemeClosedCycleOpenRestriction_apply,
    ClosedSupportedLift.BundleCycles.schemeClosed_forget_restrictCycle Y F d c hc]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassOpenPullback.BundleCycles
