import OAI.Analysis.PDE.Elliptic.Boundary.FieldCalculus
import OAI.Analysis.PDE.Dirichlet.RealOperator

/-! Quantitative commutator bounds for genuine variable tangent derivatives. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet InnerProductSpace Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hessianOperator_field_error_bound {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) (x : E) :
    ‖fderiv ℝ (gradient (fieldDerivative u T)) x -
        fderiv ℝ (gradient (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x))) x‖ ≤
      2 * ‖fderiv ℝ (gradient u) x‖ * ‖fderiv ℝ T x‖ +
      ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 2 T x‖ := by
  rw [hessianOperator_fieldDerivative hu hT]
  have he : fderiv ℝ (gradient (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x))) x +
      (fderiv ℝ T x).adjoint.comp (fderiv ℝ (gradient u) x) +
      (fderiv ℝ (gradient u) x).comp (fderiv ℝ T x) +
      fderiv ℝ (gradient (fun y => fderiv ℝ u x (T y))) x -
      fderiv ℝ (gradient (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x))) x =
      (fderiv ℝ T x).adjoint.comp (fderiv ℝ (gradient u) x) +
      (fderiv ℝ (gradient u) x).comp (fderiv ℝ T x) +
      fderiv ℝ (gradient (fun y => fderiv ℝ u x (T y))) x := by abel
  rw [he]
  have h1 := (fderiv ℝ T x).adjoint.opNorm_comp_le (fderiv ℝ (gradient u) x)
  rw [ContinuousLinearMap.adjoint.norm_map] at h1
  have h2 := (fderiv ℝ (gradient u) x).opNorm_comp_le (fderiv ℝ T x)
  have h3 := hessian_linear_comp_norm (x := x) (fderiv ℝ u x) hT.contDiffAt
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans (by nlinarith)

theorem ellipticTrace_field_bound (A : E → E →L[ℝ] E) {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) (x : E) :
    |ellipticTrace A (fieldDerivative u T) x| ≤
      |ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x)) x| +
      Module.finrank ℝ E * ‖A x‖ *
        (2 * ‖fderiv ℝ (gradient u) x‖ * ‖fderiv ℝ T x‖ +
          ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 2 T x‖) := by
  let D := fderiv ℝ (gradient (fieldDerivative u T)) x -
    fderiv ℝ (gradient (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x))) x
  have he : ellipticTrace A (fieldDerivative u T) x -
      ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x)) x =
      LinearMap.trace ℝ E ((A x).comp D).toLinearMap := by
    simp [ellipticTrace, D, ContinuousLinearMap.comp_sub, ContinuousLinearMap.toLinearMap_sub]
  have ht := (abs_trace_le_finrank_norm ((A x).comp D)).trans
    (mul_le_mul_of_nonneg_left ((A x).opNorm_comp_le D) (Nat.cast_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (hessianOperator_field_error_bound hu hT x)
    (mul_nonneg (Nat.cast_nonneg (Module.finrank ℝ E)) (norm_nonneg (A x)))
  have htriangle := abs_sub_le (ellipticTrace A (fieldDerivative u T) x)
    (ellipticTrace A (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x)) x) 0
  rw [sub_zero, sub_zero, he] at htriangle
  dsimp only [D] at ht
  nlinarith

theorem fderiv_fieldDerivative_bound {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 2 u) (hT : Differentiable ℝ T) (x : E) :
    ‖fderiv ℝ (fieldDerivative u T) x‖ ≤
      ‖fderiv ℝ u x‖ * ‖fderiv ℝ T x‖ + ‖fderiv ℝ (gradient u) x‖ * ‖T x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he := directionalDerivative_fieldDerivative hu hT v x
  change fderiv ℝ (fieldDerivative u T) x v = _ at he
  rw [he, ← inner_fderiv_gradient_at hu.contDiffAt]
  have h1 := (fderiv ℝ u x).le_opNorm (fderiv ℝ T x v)
  have h2 := (fderiv ℝ T x).le_opNorm v
  have h3 := abs_real_inner_le_norm (fderiv ℝ (gradient u) x v) (T x)
  have h4 := (fderiv ℝ (gradient u) x).le_opNorm v
  have hh := norm_add_le (fderiv ℝ u x (fderiv ℝ T x v))
    (inner ℝ (fderiv ℝ (gradient u) x v) (T x))
  calc
    _ ≤ ‖fderiv ℝ u x (fderiv ℝ T x v)‖ + |inner ℝ (fderiv ℝ (gradient u) x v) (T x)| := hh
    _ ≤ ‖fderiv ℝ u x‖ * (‖fderiv ℝ T x‖ * ‖v‖) +
        (‖fderiv ℝ (gradient u) x‖ * ‖v‖) * ‖T x‖ :=
      add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
        (h3.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)))
    _ = _ := by ring

theorem log_equation_fieldDerivative_bound {n : ℕ}
    {u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hf : DifferentiableAt ℝ f x)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      =ᶠ[nhds x] f) :
    |ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (fieldDerivative u T) x| ≤
    ‖fderiv ℝ f x‖ * ‖T x‖ / |f x| +
      Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) *
        ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)‖ *
        (2 * ‖fderiv ℝ (gradient u) x‖ * ‖fderiv ℝ T x‖ +
          ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 2 T x‖) := by
  have hd := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) (T x)
  have hid : ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y))
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x)) x = OAI.Analysis.PDE.Dirichlet.directionalDerivative f (T x) x / f x := by
    rw [OAI.Analysis.PDE.Dirichlet.logRealOperator_linearization _ hd, OAI.Analysis.PDE.Dirichlet.mooreLinearization_directional_eq hu (T x) hf heq,
      heq.eq_of_nhds]
  have hb := ellipticTrace_field_bound
    (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) hu hT x
  rw [hid, abs_div] at hb
  exact hb.trans (add_le_add
    (div_le_div_of_nonneg_right (show |OAI.Analysis.PDE.Dirichlet.directionalDerivative f (T x) x| ≤
      ‖fderiv ℝ f x‖ * ‖T x‖ from (fderiv ℝ f x).le_opNorm (T x)) (abs_nonneg _)) le_rfl)

end OAI.Analysis.PDE.Elliptic
