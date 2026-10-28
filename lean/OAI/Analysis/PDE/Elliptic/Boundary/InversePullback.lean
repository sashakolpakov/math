import OAI.Analysis.PDE.Elliptic.Boundary.PullbackBounds

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem clm_left_inverse_comm (D J : E →L[ℝ] E)
    (hJD : J.comp D = ContinuousLinearMap.id ℝ E) : D.comp J = ContinuousLinearMap.id ℝ E := by
  have hleft : Function.LeftInverse J D := fun v => congrArg (fun T : E →L[ℝ] E => T v) hJD
  have hsurj : Function.Surjective D := LinearMap.surjective_of_injective (f := D.toLinearMap) hleft.injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  change D (J (D w)) = D w
  rw [hleft w]

theorem inverse_jacobian_of_local_right_inverse {P F : E → E} {y : E}
    (hP : DifferentiableAt ℝ P (F y)) (hF : DifferentiableAt ℝ F y)
    (hinv : (fun z => P (F z)) =ᶠ[𝓝 y] id) :
    (fderiv ℝ F y).comp (fderiv ℝ P (F y)) = ContinuousLinearMap.id ℝ E := by
  apply clm_left_inverse_comm
  have hcomp := (hP.hasFDerivAt.comp y hF.hasFDerivAt).fderiv
  have he := hinv.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (P ∘ F) y = fderiv ℝ id y at he
  rw [hcomp] at he
  simpa using he

theorem pullbackEllipticOperator_comp (D J A : E →L[ℝ] E) :
    pullbackEllipticOperator D (pullbackEllipticOperator J A) =
      pullbackEllipticOperator (D.comp J) A := by
  ext v
  simp [pullbackEllipticOperator, ContinuousLinearMap.adjoint_comp]

theorem pullbackEllipticOperator_inverse (D J A : E →L[ℝ] E)
    (hDJ : D.comp J = ContinuousLinearMap.id ℝ E) :
    pullbackEllipticOperator D (pullbackEllipticOperator J A) = A := by
  rw [pullbackEllipticOperator_comp, hDJ]
  simp [pullbackEllipticOperator, ContinuousLinearMap.adjoint_id]

theorem ellipticTrace_inverse_pullback (A : E → E →L[ℝ] E) {P F : E → E} {u : E → ℝ} {y : E}
    (hP : DifferentiableAt ℝ P (F y)) (hF : ContDiffAt ℝ 2 F y) (hu : ContDiffAt ℝ 2 u (F y))
    (hinv : (fun z => P (F z)) =ᶠ[𝓝 y] id) :
    ellipticTrace (fun z => pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z)))
      (fun z => u (F z)) y =
    ellipticTrace A u (F y) +
      ellipticTrace (fun z => pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z)))
        (fun z => fderiv ℝ u (F y) (F z)) y := by
  rw [ellipticTrace_comp _ hu hF]
  rw [pullbackEllipticOperator_inverse _ _ _
    (inverse_jacobian_of_local_right_inverse hP (hF.differentiableAt (by norm_num)) hinv)]
  rfl

theorem ellipticTrace_inverse_pullback_bound (A : E → E →L[ℝ] E) {P F : E → E} {u : E → ℝ} {y : E}
    (hP : DifferentiableAt ℝ P (F y)) (hF : ContDiffAt ℝ 2 F y) (hu : ContDiffAt ℝ 2 u (F y))
    (hinv : (fun z => P (F z)) =ᶠ[𝓝 y] id) :
    |ellipticTrace (fun z => pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z)))
      (fun z => u (F z)) y| ≤
    |ellipticTrace A u (F y)| +
      Module.finrank ℝ E * ‖pullbackEllipticOperator (fderiv ℝ P (F y)) (A (F y))‖ *
        ‖fderiv ℝ u (F y)‖ * ‖iteratedFDeriv ℝ 2 F y‖ := by
  rw [ellipticTrace_inverse_pullback A hP hF hu hinv]
  exact (abs_add_le _ _).trans (add_le_add_right (ellipticTrace_linear_comp_bound _ _ hF) _)

end OAI.Analysis.PDE.Elliptic
