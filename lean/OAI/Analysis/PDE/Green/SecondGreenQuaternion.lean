import OAI.Analysis.PDE.Green.SecondGreen
import OAI.LinearAlgebra.Moore.Normal

/-! Quaternionic second Green identity with vanishing normal cofactor. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem quaternion_current_second_green {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 → (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0) :
    (∫ x in {x | r x < 0}, u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      ∫ x in {x | r x < 0}, v x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hKs (p q : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q = OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) q p :=
    (congrFun (congrFun (OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm e (A x) (hAh x)) p) q).symm
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have hn (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : r x = 0) :
      (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        (fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) * fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector q))) = 0 := by
    rw [realCoefficients_quadratic]
    exact hnormal x hx
  have h := real_operator_second_green OAI.Analysis.PDE.Dirichlet.coordinateVector
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hKs hd hb hrne huz hn
  have he (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian f x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian f x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hf.contDiffAt)
  simpa only [he u hu, he v hv, OAI.Analysis.PDE.Dirichlet.realHessian] using h

/-- The cofactor form of the second Green identity. No positivity of the full
quaternionic Hessian is used or assumed. -/
theorem moore_cofactor_second_green {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 → (OAI.Analysis.PDE.Dirichlet.quaternionForm
      (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x)).re = 0) :
    (∫ x in {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  have hA : ContDiff ℝ 1 (fun x => OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_second_green e hA (fun _ => OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)
    (fun x b => OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt b)
    hu hv hr hb hrne huz hnormal
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt),
    OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hu.contDiffAt)] using h

/-- A singular tangential restriction supplies the zero-normal boundary
condition algebraically. This is the form needed for the determinant pencil. -/
theorem moore_cofactor_second_green_of_tangential_kernel {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {ψ r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hkernel : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0 ∧ ∃ a : Quaternion ℝ,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x *ᵥ w = fun i => OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x i * a) :
    (∫ x in {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  apply moore_cofactor_second_green e hψ hu hv hr hb hrne huz
  intro x hx
  obtain ⟨w, hw, horth, a, ha⟩ := hkernel x hx
  exact OAI.LinearAlgebra.Moore.mooreCofactor_normal_zero_of_tangential_kernel _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e (hψ.of_le (by norm_num)).contDiffAt)
    _ w hw horth a ha

end OAI.Analysis.PDE.Green
