import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanCoefficientHolder

open InnerProductSpace Set Filter
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem toEuclideanCLM_euclideanCoefficientMatrix (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCoefficientMatrix A) = A := by
  apply ContinuousLinearMap.ext
  intro x
  let b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have hrepr := A.toLinearMap.toMatrix_mulVec_repr b b x
  have hmul : (euclideanCoefficientMatrix A).mulVec (x : Fin m → ℝ) = (A x : Fin m → ℝ) := by
    rw [euclideanCoefficientMatrix_eq_toMatrix A hA]
    exact hrepr
  ext i
  exact (congrFun (Matrix.ofLp_toEuclideanCLM (euclideanCoefficientMatrix A) x) i).trans
    (congrFun hmul i)

/-- Symmetry is preserved by the actual Jacobian congruence. -/
theorem pullback_coefficient_isSymmetric (J A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (J (A (J.adjoint x))) y = inner ℝ x (J (A (J.adjoint y)))
  rw [← J.adjoint_inner_right, ← J.adjoint_inner_left]
  exact hA _ _

/-- The equation after flattening a curved boundary, with the principal
coefficient and drift replaced by their constructed Hölder representatives. -/
theorem chart_nondivergence_equation {α : ℝ}
    (A : E → E →L[ℝ] E) (G P : E → E) (u : E → ℝ)
    (hG : ContDiff ℝ 2 G) (hP : ContDiff ℝ 1 P) (hu : ContDiff ℝ 2 u)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α)
    (x : E) (hA : (A (G x)).toLinearMap.IsSymmetric)
    (hinv : (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (hB : OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = euclideanCoefficientMatrix
      (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))))
    (hb : OAI.Analysis.Normed.Function.Holder.HolderMap.value b x = OAI.Analysis.PDE.Elliptic.inverseChartDrift A G P x) :
    nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) (fun y => u (G y)) x =
      OAI.Analysis.PDE.Elliptic.ellipticTrace A u (G x) +
        fderiv ℝ (fun y => u (G y)) x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b x) := by
  let C := fun y => OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y))
  have hs : (C x).toLinearMap.IsSymmetric := pullback_coefficient_isSymmetric _ _ hA
  have he := ellipticTrace_eq_nondivergenceOperator C (fun y => u (G y)) (hu.comp hG) x hs
  have hc : nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) (fun y => u (G y)) x =
      nondivergenceOperator (fun y => euclideanCoefficientMatrix (C y)) (fun y => u (G y)) x := by
    simp only [nondivergenceOperator, hB, C]
  rw [hc, ← he, hb]
  exact OAI.Analysis.PDE.Elliptic.ellipticTrace_inverse_chart_with_drift A
    (hP.differentiable one_ne_zero (G x)) hG.contDiffAt hu.contDiffAt hinv

end OAI.Analysis.PDE.Schauder
