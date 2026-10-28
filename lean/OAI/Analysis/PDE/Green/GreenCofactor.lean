import OAI.Analysis.PDE.Green.GreenAlgebra
import OAI.Analysis.PDE.Green.GreenOperator
import OAI.Analysis.Calculus.Quaternion.CofactorDivergence

/-! The actual quaternionic cofactor Green identity for compactly supported tests. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem fderiv_realCoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n s : ℕ} (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s)
    {A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x v =
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (fderiv ℝ A x v) p q := by
  have h := ((realCoefficientCLM e p q).hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  exact congrArg (fun L => L v) h

theorem contDiff_quaternionHessian_one {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ) :
    ContDiff ℝ 1 (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hH : ContDiff ℝ 1 (OAI.Analysis.PDE.Dirichlet.realHessian ψ) := by
    apply contDiff_pi.mpr
    intro p
    apply contDiff_pi.mpr
    intro q
    exact (hD.clm_apply contDiff_const).clm_apply contDiff_const
  exact (OAI.Analysis.Calculus.Quaternion.hessianCLM e).contDiff.comp hH

theorem quaternion_current_green {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p ↦ fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hs : HasCompactSupport u) :
    (∫ x, u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      ∑ p, fderiv ℝ (fun y ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_green (μ := volume) OAI.Analysis.PDE.Dirichlet.coordinateVector
    (fun p q x ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hs hd
  have he (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) : OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian v x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian v x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hv.contDiffAt)
  simpa only [he, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.realGradient] using h

/-- The cofactor Green identity is derived from its proved pointwise divergence;
it is not an additional assumption on the potential. -/
theorem moore_cofactor_green {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hs : HasCompactSupport u) :
    (∫ x, u x * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hA : ContDiff ℝ 1 (fun x ↦ OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_green e hA
    (fun x b ↦ OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt b) hu hv hs
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt)] using h

/-- The quadratic Green identity, with the actual quaternionic gradient. -/
theorem moore_cofactor_energy_identity {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) :
    (∫ x, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x, (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x))
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have h := moore_cofactor_green e hψ (hu.of_le (by norm_num)) hu hs
  have he (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient u x q) =
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x))
          (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
    simp_rw [mul_assoc]
    exact realCoefficients_quadratic _ e (OAI.Analysis.PDE.Dirichlet.realGradient u x)
  simp_rw [he] at h
  simp_rw [neg_mul]
  rw [integral_neg, h, neg_neg]

theorem moore_cofactor_energy_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u)
    (hpos : ∀ x, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)).PosSemidef) :
    0 ≤ ∫ x, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [moore_cofactor_energy_identity e hψ hu hs]
  apply integral_nonneg
  intro x
  exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)).mp
    (OAI.LinearAlgebra.Moore.mooreCofactor_posSemidef _ (hpos x)) _

end OAI.Analysis.PDE.Green
