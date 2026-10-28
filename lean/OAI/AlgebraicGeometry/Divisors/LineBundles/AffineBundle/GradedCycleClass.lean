import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.OverGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass

/-! # Graded Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedCycleClass.Cycles

noncomputable section

/-! The cycle-class comparison for actual affine-space bundles is
linear on all finite dimension-graded cycles, with every coefficient
and the exact dimension shift retained. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
    (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank f.left r)
    (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "he" => OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.OverGrading.Cycles.affineBundleOver_complementDegree f r h d p hd

theorem affineBundleGradedPointClass (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X (irreducibleSetEquivPoints.symm x.val) p
        ((congrArg (fun n => n + p) x.property).trans hd)) =
    Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass E (irreducibleSetEquivPoints.symm (OverGrading.Cycles.affineBundleOverDimensionPoint f r h d x).val) p
      ((congrArg (fun n => n + p) (OverGrading.Cycles.affineBundleOverDimensionPoint f r h d x).property).trans he) := by
  have hs : Integral.PulledSupport.BundleCycles.integralPulledSupport f.left (irreducibleSetEquivPoints.symm x.val) =
      irreducibleSetEquivPoints.symm (OverGrading.Cycles.affineBundleOverDimensionPoint f r h d x).val := by
    rw [Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure, irreducibleSetEquivPoints.apply_symm_apply]
    rfl
  exact (AbsoluteClass.Cycles.schemeCycleClass_affineBundle f h.forget (irreducibleSetEquivPoints.symm x.val) p
    ((congrArg (fun n => n + p) x.property).trans hd)).trans
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeCycleClass_congrSupport E _ _ hs p _ _)

theorem schemeGradedCycleClass_affineBundle :
    (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass E (d + r) p he).comp (OverGrading.Cycles.affineBundleOverGradedExtension f r h d) =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f).hom.comp (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hd) := by
  apply Finsupp.lhom_ext
  intro x a
  change Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass E (d + r) p he
    (OverGrading.Cycles.affineBundleOverGradedExtension f r h d (Finsupp.single x a)) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hd (Finsupp.single x a))
  rw [OverGrading.Cycles.affineBundleOverGradedExtension_single, Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single,
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single, map_smul]
  exact congrArg (fun b => a • b) (affineBundleGradedPointClass f r h d p hd x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedCycleClass.Cycles
