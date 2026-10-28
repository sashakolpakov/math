import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationCanonicalGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalCycleClassZero

/-! # Presentation Graded Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedClass.BundleCycles

noncomputable section

/-! On the exact dimension grade of an integral presentation, the canonical class of every finite cycle is the independently defined geometric presentation class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] (p d : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap)

theorem presentationGradedCycle_class (z : X.RationalDimensionCycle p) :
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X.toOver d p hd (PresentationGradedCycle.BundleCycles.presentationGradedCycle X p d hd z) =
      X.geometricCycleClassMap p z := by
  classical
  let L : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.structureMap d →₀ ℚ) →ₗ[ℚ] X.rationalCohomology (p + p) :=
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X.toOver d p hd
  change L (PresentationGradedCycle.BundleCycles.presentationGradedCycle X p d hd z) = _
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single Z r =>
    have hs := Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single X.toOver d p hd (PresentationGradedCycle.BundleCycles.presentationDimensionPoint X p d hd Z) r
    have he : irreducibleSetEquivPoints.symm (PresentationGradedCycle.BundleCycles.presentationDimensionPoint X p d hd Z).val = Z.val :=
      OrderIso.symm_apply_apply _ _
    have h := (Scheme.GradedAbsoluteClass.BundleCycles.schemeCycleClass_congrSupport X.toOver _ _ he p
      ((congrArg (fun n => n + p) (PresentationGradedCycle.BundleCycles.presentationDimensionPoint X p d hd Z).property).trans hd)
      (PresentationComponentSupportClass.BundleCycles.integralPresentationSupport_dimension X p Z)).trans (PresentationCanonicalGenerator.BundleCycles.integralPresentation_cycleSupportClass X p Z)
    have hr : Finsupp.single Z r = r • Finsupp.single Z (1 : ℚ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (congrArg L (PresentationGradedCycle.BundleCycles.presentationGradedCycle_single X p d hd Z r)).trans
      (hs.trans ((congrArg (fun b => r • b) h).trans
        ((map_smul (X.geometricCycleClassMap p) r (Finsupp.single Z 1)).symm.trans
          (congrArg (X.geometricCycleClassMap p) hr.symm))))

theorem presentationPointChow_class (z : X.RationalDimensionCycle p) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass X.toOver d p hd (Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d (Chow.BundleCycles.pointCycle X p z)) =
      X.geometricCycleClassMap p z := by
  rw [PresentationGradedCycle.BundleCycles.presentationGradedCycle_chow X p d hd]
  exact presentationGradedCycle_class X p d hd z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedClass.BundleCycles
