import OAI.Analysis.PDE.Green.BoundaryExtension
import OAI.Analysis.PDE.Green.GreenCofactor

/-! Cofactor Green and energy identities with genuine zero boundary values. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Matrix _root_.MeasureTheory Measure OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem hasCompactSupport_realFlux {E I : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype I] (d : I → E) (K : I → I → E → ℝ)
    {v : E → ℝ} (hv : HasCompactSupport v) (i : I) :
    HasCompactSupport (realFlux d K v i) := by
  apply (hv.fderiv ℝ).mono'
  intro x hx
  by_contra hn
  have hz : fderiv ℝ v x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  simp only [realFlux, hz, _root_.zero_apply, mul_zero, Finset.sum_const_zero]

theorem real_operator_green_zero_boundary {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype I]
    {μ : Measure E} [IsAddHaarMeasure μ] {S : Set E}
    (hS : IsOpen S) (hnull : μ (frontier S) = 0)
    (d : I → E) (K : I → I → E → ℝ) {u v : E → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0) :
    (∫ x in S, u x * (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j)) ∂μ) =
      -(∫ x in S, ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) ∂μ) := by
  have h := integral_divergence_by_parts_zero_boundary hS hnull hu hsu hz d
    (realFlux d K v) (contDiff_realFlux d K hK hv) (hasCompactSupport_realFlux d K hsv)
  simp_rw [realFlux_divergence d K hK hv hdiv] at h
  convert h using 3
  simp only [realFlux, Finset.mul_sum]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- First Green identity for a conserved quaternionic matrix field on a domain. -/
theorem quaternion_current_green_zero_boundary {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hnull : volume (frontier S) = 0)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p ↦ fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x in S, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      ∑ p, fderiv ℝ (fun y ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_green_zero_boundary hS hnull OAI.Analysis.PDE.Dirichlet.coordinateVector
    (fun p q x ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hsu hsv hz hd
  have he (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) : OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian v x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian v x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hv.contDiffAt)
  simpa only [he, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.realGradient] using h

/-- Actual cofactor Green identity for zero boundary data. Neither positivity
nor a postulated integration-by-parts identity is required. -/
theorem moore_cofactor_green_zero_boundary {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hnull : volume (frontier S) = 0)
    {ψ u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x in S, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hA : ContDiff ℝ 1 (fun x ↦ OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_green_zero_boundary e hS hnull hA
    (fun x b ↦ OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt b)
    hu hv hsu hsv hz
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt)] using h

/-- Domain energy equals the nonnegative cofactor gradient form; the test
function may reach the boundary and only its boundary value is prescribed. -/
theorem moore_cofactor_energy_zero_boundary {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hnull : volume (frontier S) = 0)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x))
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have h := moore_cofactor_green_zero_boundary e hS hnull hψ
    (hu.of_le (by norm_num)) hu hs hs hz
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

theorem moore_cofactor_energy_zero_boundary_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hnull : volume (frontier S) = 0)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)).PosSemidef) :
    0 ≤ ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [moore_cofactor_energy_zero_boundary e hS hnull hψ hu hs hz]
  apply setIntegral_nonneg hS.measurableSet
  intro x hx
  exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)).mp
    (OAI.LinearAlgebra.Moore.mooreCofactor_posSemidef _ (hpos x hx)) _

end OAI.Analysis.PDE.Green
