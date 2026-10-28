import OAI.Analysis.PDE.Elliptic.Boundary.FieldBounds
import OAI.Analysis.PDE.Elliptic.HessianNorm
import OAI.Analysis.PDE.Elliptic.Boundary.Correction

/-! The prescribed nonzero boundary data contribute a fixed smooth forcing
term; they are subtracted explicitly from the differentiated equation. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Filter Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem fieldDerivative_sub {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (T : E → E) : fieldDerivative (fun x => f x - g x) T =
      fun x => fieldDerivative f T x - fieldDerivative g T x := by
  funext x
  unfold fieldDerivative
  rw [show fderiv ℝ (fun x => f x - g x) x = fderiv ℝ f x - fderiv ℝ g x from
    ((hf x).hasFDerivAt.sub (hg x).hasFDerivAt).fderiv]
  rfl

theorem ellipticTrace_sub (A : E → E →L[ℝ] E) {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    ellipticTrace A (fun y => f y - g y) x = ellipticTrace A f x - ellipticTrace A g x := by
  simpa only [neg_one_smul, sub_eq_add_neg, neg_one_mul] using ellipticTrace_add_smul A hf hg (-1) x

theorem ellipticTrace_abs_norm_bound (A : E → E →L[ℝ] E) (f : E → ℝ) (x : E) :
    |ellipticTrace A f x| ≤ Module.finrank ℝ E * ‖A x‖ * ‖fderiv ℝ (gradient f) x‖ := by
  have hb := mul_le_mul_of_nonneg_left ((A x).opNorm_comp_le (fderiv ℝ (gradient f) x))
    (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E))
  exact (abs_trace_le_finrank_norm ((A x).comp (fderiv ℝ (gradient f) x))).trans
    (by simpa only [mul_assoc] using hb)

theorem log_equation_field_remainder_bound {n : ℕ}
    {ψ B f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hψ : ContDiff ℝ 3 ψ) (hB : ContDiff ℝ 3 B) (hT : ContDiff ℝ 2 T) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hf : DifferentiableAt ℝ f x)
    (heq : (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) =ᶠ[𝓝 x] f) :
    |ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y))
      (fieldDerivative (fun y => ψ y - B y) T) x| ≤
      ‖fderiv ℝ f x‖ * ‖T x‖ / |f x| +
      Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ *
        (2 * ‖fderiv ℝ (gradient ψ) x‖ * ‖fderiv ℝ T x‖ +
          ‖fderiv ℝ ψ x‖ * ‖iteratedFDeriv ℝ 2 T x‖ +
          ‖fderiv ℝ (gradient (fieldDerivative B T)) x‖) := by
  rw [fieldDerivative_sub (hψ.differentiable (by norm_num)) (hB.differentiable (by norm_num)),
    ellipticTrace_sub _ (contDiff_fieldDerivative hψ hT (by norm_num))
      (contDiff_fieldDerivative hB hT (by norm_num))]
  have hmain := log_equation_fieldDerivative_bound hψ hT hf heq
  have hback := ellipticTrace_abs_norm_bound
    (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) (fieldDerivative B T) x
  have ht := abs_sub_le
    (ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) (fieldDerivative ψ T) x)
    0 (ellipticTrace (fun y => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) (fieldDerivative B T) x)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  nlinarith

theorem exists_background_field_bounds {B : E → ℝ} {T : E → E}
    (hB : ContDiff ℝ 3 B) (hT : ContDiff ℝ 2 T) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      ‖fderiv ℝ (fieldDerivative B T) x‖ ≤ C ∧
      ‖fderiv ℝ (gradient (fieldDerivative B T)) x‖ ≤ C := by
  have hW : ContDiff ℝ 2 (fieldDerivative B T) := contDiff_fieldDerivative hB hT (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ (fieldDerivative B T)) := hW.fderiv_right (by norm_num)
  have hc2 : Continuous (fun x => ‖iteratedFDeriv ℝ 2 (fieldDerivative B T) x‖) :=
    continuous_iff_continuousAt.mpr fun x => (hW.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hD.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max 1 (max C1 C2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  refine ⟨(hC1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  rw [norm_fderiv_gradient hW]
  have hi : ‖iteratedFDeriv ℝ 2 (fieldDerivative B T) x‖ ≤ C2 := by simpa using hC2 x hx
  have hh := (second_fderiv_norm_le_iterated x).trans hi
  exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem field_remainder_fderiv_bound {ψ B : E → ℝ} {T : E → E}
    (hψ : ContDiff ℝ 3 ψ) (hB : ContDiff ℝ 3 B) (hT : ContDiff ℝ 2 T) (x : E) :
    ‖fderiv ℝ (fieldDerivative (fun y => ψ y - B y) T) x‖ ≤
      ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ T x‖ + ‖fderiv ℝ (gradient ψ) x‖ * ‖T x‖ +
        ‖fderiv ℝ (fieldDerivative B T) x‖ := by
  have hp := (contDiff_fieldDerivative hψ hT (by norm_num)).differentiable (by norm_num) x
  have hb := (contDiff_fieldDerivative hB hT (by norm_num)).differentiable (by norm_num) x
  rw [fieldDerivative_sub (hψ.differentiable (by norm_num)) (hB.differentiable (by norm_num))]
  rw [show fderiv ℝ (fun y => fieldDerivative ψ T y - fieldDerivative B T y) x =
    fderiv ℝ (fieldDerivative ψ T) x - fderiv ℝ (fieldDerivative B T) x from
      (hp.hasFDerivAt.sub hb.hasFDerivAt).fderiv]
  exact (norm_sub_le _ _).trans (add_le_add
    (fderiv_fieldDerivative_bound (hψ.of_le (by norm_num)) (hT.differentiable (by norm_num)) x) le_rfl)

end OAI.Analysis.PDE.Elliptic
