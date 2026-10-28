import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.RegularSmoothness
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldInverse
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence

/-! # Smooth Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation

noncomputable section

/-! Smooth evaluation on all actual analytic opens, including the empty open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

instance openOverIntegral (U : X.left.Opens) [Nonempty U] : IsIntegral (AffineIsoEvaluation.openOver X U).left :=
  inferInstanceAs (IsIntegral U.toScheme)

instance openOverSmooth (U : X.left.Opens) : Smooth (AffineIsoEvaluation.openOver X U).hom :=
  inferInstanceAs (Smooth (U.ι ≫ X.hom))

/-- The inverse open-point homeomorphism is smooth for the actual native manifolds. -/
theorem openPointHomeomorph_symm_smooth (U : X.left.Opens) [Nonempty U] :
    ContMDiff 𝓘(ℝ, RegularSmoothness.NativeModel X) 𝓘(ℝ, RegularSmoothness.NativeModel (AffineIsoEvaluation.openOver X U)) ∞
      (AffineIsoEvaluation.openPointHomeomorph X U).symm := by
  have hf : IsLocalDiffeomorph 𝓘(ℝ, RegularSmoothness.NativeModel (AffineIsoEvaluation.openOver X U)) 𝓘(ℝ, RegularSmoothness.NativeModel X) ω
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AffineIsoEvaluation.openInclusion X U)) := by
    intro p
    exact ManifoldInverse.Smooth.isLocalDiffeomorphAt_of_realAnalytic_bijective_mfderiv _
      (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (AffineIsoEvaluation.openInclusion X U) ω) p
      (ComplexPoints.Analytic.IntrinsicOpenDifferential.real_mfderiv_nativeScheme_openImmersion_bijective (AffineIsoEvaluation.openInclusion X U) p)
  apply ManifoldInverse.Smooth.contMDiff_lift_of_localDiffeomorph _ hf
    (AffineIsoEvaluation.openPointHomeomorph X U).symm (AffineIsoEvaluation.openPointHomeomorph X U).symm.continuous
  have heq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AffineIsoEvaluation.openInclusion X U) ∘ (AffineIsoEvaluation.openPointHomeomorph X U).symm =
      (Subtype.val : AffineIsoEvaluation.analyticOpen X U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
    funext p
    exact (AffineIsoEvaluation.openPointHomeomorph_val X U ((AffineIsoEvaluation.openPointHomeomorph X U).symm p)).symm.trans
      (congrArg Subtype.val ((AffineIsoEvaluation.openPointHomeomorph X U).apply_symm_apply p))
  rw [heq]
  exact contMDiff_subtype_val (I := 𝓘(ℝ, RegularSmoothness.NativeModel X))

/-- Every algebraic section gives a smooth function on the corresponding intrinsic open manifold. -/
theorem sectionEvaluationOn_smooth (U : X.left.Opens) (a : Γ(X.left, U)) :
    ContMDiff 𝓘(ℝ, RegularSmoothness.NativeModel X) 𝓘(ℝ, ℂ) ∞ (AffineIsoEvaluation.sectionEvaluationOn X U a) := by
  classical
  by_cases hU : Nonempty U
  · let : Nonempty U := hU
    exact (RegularSmoothness.globalEvaluation_real_contMDiff (AffineIsoEvaluation.openOver X U) (U.topIso.inv a) ∞).comp
      (openPointHomeomorph_symm_smooth X U)
  · intro p
    exact (hU ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p.val, p.property⟩⟩).elim

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation
