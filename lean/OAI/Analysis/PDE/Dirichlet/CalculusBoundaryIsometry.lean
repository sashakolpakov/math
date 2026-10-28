import OAI.Analysis.PDE.Dirichlet.SchauderIsometryEquation

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isometryConjugate_adjoint (e : E ≃ₗᵢ[ℝ] F) (A : F →L[ℝ] F) :
    (isometryConjugate e A).adjoint = isometryConjugate e A.adjoint := by
  ext v
  apply ext_inner_right ℝ
  intro w
  calc
    inner ℝ ((isometryConjugate e A).adjoint v) w = inner ℝ v (isometryConjugate e A w) :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner ℝ (e v) (A (e w)) := by
      rw [← e.inner_map_map]
      simp only [isometryConjugate_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℝ (A.adjoint (e v)) (e w) := (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = inner ℝ (isometryConjugate e A.adjoint v) w := (inner_isometryConjugate e A.adjoint v w).symm

theorem isometryConjugate_pullback (e : E ≃ₗᵢ[ℝ] F) (J A : F →L[ℝ] F) :
    isometryConjugate e (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A) =
      OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (isometryConjugate e J) (isometryConjugate e A) := by
  unfold OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator
  rw [isometryConjugate_adjoint]
  ext v
  simp only [ContinuousLinearMap.comp_apply, isometryConjugate_apply,
    LinearIsometryEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_isometry_conjugate_map (e : E ≃ₗᵢ[ℝ] F) (P : F → F)
    (hP : Differentiable ℝ P) (x : E) :
    fderiv ℝ (fun z => e.symm (P (e z))) x = isometryConjugate e (fderiv ℝ P (e x)) := by
  exact (e.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hP (e x)).hasFDerivAt.comp x e.toContinuousLinearEquiv.hasFDerivAt)).fderiv

/-- The transported principal coefficient is exactly the coefficient of
the corresponding chart in the flat Euclidean coordinate model. -/
theorem isometryConjugate_chart_coefficient (e : E ≃ₗᵢ[ℝ] F) (G P : F → F)
    (hP : Differentiable ℝ P) (A : F → F →L[ℝ] F) (x : E) :
    isometryConjugate e (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (fderiv ℝ P (G (e x))) (A (G (e x)))) =
      OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator
        (fderiv ℝ (fun z => e.symm (P (e z))) (e.symm (G (e x))))
        (isometryConjugate e (A (G (e x)))) := by
  rw [fderiv_isometry_conjugate_map e P hP, e.apply_symm_apply, isometryConjugate_pullback]

end OAI.Analysis.PDE.Dirichlet
