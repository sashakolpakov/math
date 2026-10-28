import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormPurity

/-! # Holomorphic Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicForms

noncomputable section

/-! All genuine algebraic forms, on globals and on each Zariski open, realize in type (n,0). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem globalSmoothFormMap_pure (n : ℕ) (a : Forms.Form Γ(X.left, ⊤) n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n 0
      (GlobalSmoothCochain.globalSmoothFormMap X n a).val :=
  Holomorphic.FormPurity.Smooth.smoothFormMap_pure (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)
    (fun s => RegularSmoothness.globalEvaluation_contMDiff X s ∞) n a

theorem openSmoothFormMap_intrinsic_pure (U : X.left.Opens) (n : ℕ)
    (a : Forms.Form Γ(X.left, U) n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n 0
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n)
        (Open.SmoothForms.openSmoothFormMap X U n a)).val := by
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n 0
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n).symm
        (Betti.Smooth.CochainMap.smoothFormMap (Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) n a))).val
  rw [LinearEquiv.apply_symm_apply]
  exact Holomorphic.FormPurity.Smooth.smoothFormMap_pure (Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U) n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicForms
