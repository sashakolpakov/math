import OAI.Analysis.PDE.Elliptic.Boundary.FixedChart
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Error

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem pullbackEllipticOperator_variation (J K A B : E →L[ℝ] E) :
    ‖pullbackEllipticOperator J A - pullbackEllipticOperator K B‖ ≤
      ‖J‖^2 * ‖A-B‖ + ‖J-K‖ * ‖B‖ * ‖J‖ + ‖K‖ * ‖B‖ * ‖J-K‖ := by
  have hid : pullbackEllipticOperator J A - pullbackEllipticOperator K B =
      hessianCongruence J.adjoint (A-B) +
        (hessianCongruence J.adjoint B - hessianCongruence K.adjoint B) := by
    rw [hessianCongruence_sub]
    simp only [hessianCongruence, pullbackEllipticOperator, ContinuousLinearMap.adjoint_adjoint]
    abel
  rw [hid]
  have h1 := hessianCongruence_norm J.adjoint (A-B)
  have h2 := hessianCongruence_variation J.adjoint K.adjoint B
  have hJK : ‖J.adjoint-K.adjoint‖ = ‖J-K‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  simp only [ContinuousLinearMap.adjoint.norm_map, hJK] at h1 h2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- A fixed smooth coordinate change preserves the original Hölder
exponent and the linear size of the coefficient norm. -/
theorem pullback_coefficient_holder_on_unit_diameter
    (A : E → E →L[ℝ] E) (G : E → E) (J : E → E →L[ℝ] E)
    {S : Set E} {L N α : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (hAn : ∀ x ∈ S, ‖A (G x)‖ ≤ N)
    (hAh : ∀ x ∈ S, ∀ y ∈ S, ‖A (G x)-A (G y)‖ ≤ N * ‖G x-G y‖^α)
    (hJn : ∀ x ∈ S, ‖J x‖ ≤ L)
    (hJh : ∀ x ∈ S, ∀ y ∈ S, ‖J x-J y‖ ≤ L * ‖x-y‖)
    (hGh : ∀ x ∈ S, ∀ y ∈ S, ‖G x-G y‖ ≤ L * ‖x-y‖) :
    (∀ x ∈ S, ‖pullbackEllipticOperator (J x) (A (G x))‖ ≤ L^2*N) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖pullbackEllipticOperator (J x) (A (G x)) -
        pullbackEllipticOperator (J y) (A (G y))‖ ≤
          (L^2 * L^α + 2*L^2) * N * ‖x-y‖^α) := by
  constructor
  · intro x hx
    apply (pullbackEllipticOperator_norm_bound _ _).trans
    exact mul_le_mul (by nlinarith [norm_nonneg (J x), hJn x hx]) (hAn x hx)
      (norm_nonneg _) (sq_nonneg L)
  · intro x hx y hy
    have hd : ‖x-y‖ ≤ ‖x-y‖^α :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) (hdiam x hx y hy) hα1
    have hJxy : ‖J x-J y‖ ≤ L * ‖x-y‖^α :=
      (hJh x hx y hy).trans (mul_le_mul_of_nonneg_left hd hL)
    have hAxy : ‖A (G x)-A (G y)‖ ≤ N * L^α * ‖x-y‖^α := by
      calc
        _ ≤ N * ‖G x-G y‖^α := hAh x hx y hy
        _ ≤ N * (L * ‖x-y‖)^α := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hGh x hx y hy) hα) hN
        _ = N * L^α * ‖x-y‖^α := by rw [Real.mul_rpow hL (norm_nonneg _)]; ring
    calc
      _ ≤ ‖J x‖^2 * ‖A (G x)-A (G y)‖ + ‖J x-J y‖ * ‖A (G y)‖ * ‖J x‖ +
          ‖J y‖ * ‖A (G y)‖ * ‖J x-J y‖ := pullbackEllipticOperator_variation _ _ _ _
      _ ≤ L^2 * (N * L^α * ‖x-y‖^α) + (L * ‖x-y‖^α) * N * L +
          L * N * (L * ‖x-y‖^α) := by
        gcongr
        all_goals first | exact hJn x hx | exact hJn y hy | exact hAn y hy
      _ = (L^2 * L^α + 2*L^2) * N * ‖x-y‖^α := by ring

end OAI.Analysis.PDE.Elliptic
