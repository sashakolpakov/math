import OAI.Analysis.PDE.Green.BoundaryGreen

/-! Localization removes support assumptions from Green's identity on bounded domains. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Matrix Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology ContDiff Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem exists_compact_extension_on_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : Bornology.IsBounded S) {k : ℕ∞}
    {u : E → ℝ} (hu : ContDiff ℝ k u) :
    ∃ v : E → ℝ, ContDiff ℝ k v ∧ HasCompactSupport v ∧
      ∀ x ∈ closure S, v =ᶠ[𝓝 x] u := by
  obtain ⟨R,hR,hsub⟩ := hS.closure.subset_ball_lt 0 (0 : E)
  let b : ContDiffBump (0 : E) := ⟨R,R+1,hR,lt_add_one R⟩
  refine ⟨fun x ↦ b x * u x, b.contDiff.mul hu, b.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  filter_upwards [b.eventuallyEq_one_of_mem_ball (hsub hx)] with y hy
  change b y = 1 at hy
  rw [hy, one_mul]

theorem realGradient_congr_nhds {n s : ℕ} {u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s} (h : u =ᶠ[𝓝 x] v) : OAI.Analysis.PDE.Dirichlet.realGradient u x = OAI.Analysis.PDE.Dirichlet.realGradient v x := by
  funext p
  exact congrArg (fun D ↦ D (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) (h.fderiv_eq (𝕜 := ℝ))

theorem quaternionHessian_congr_nhds {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s} (h : u =ᶠ[𝓝 x] v) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x = OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x := by
  have he := (h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  rw [he]

/-- First Green identity on a bounded domain. Smooth functions need not have
compact support; their values on the boundary are the only boundary input. -/
theorem quaternion_current_green_bounded {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p ↦ fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x in S, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  obtain ⟨u',hu',hsu,heu⟩ := exists_compact_extension_on_bounded hb hu
  obtain ⟨v',hv',hsv,hev⟩ := exists_compact_extension_on_bounded hb hv
  have hzu : ∀ x ∈ frontier S, u' x = 0 := by
    intro x hx
    rw [(heu x hx.1).self_of_nhds, hz x hx]
  calc
    _ = ∫ x in S, u' x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v' x) := by
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [(heu x (subset_closure hx)).self_of_nhds,
        quaternionHessian_congr_nhds e (hev x (subset_closure hx))]
    _ = -(∫ x in S, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u' x p * OAI.Analysis.PDE.Dirichlet.realGradient v' x q) :=
      quaternion_current_green_zero_boundary e hS hnull hA hdiv hu' hv' hsu hsv hzu
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [realGradient_congr_nhds (heu x (subset_closure hx)),
        realGradient_congr_nhds (hev x (subset_closure hx))]

theorem moore_cofactor_green_bounded {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {ψ u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, u x * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
      -(∫ x in S, ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hA : ContDiff ℝ 1 (fun x ↦ OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (contDiff_quaternionHessian_one e hψ)
  have h := quaternion_current_green_bounded e hS hb hnull hA
    (fun x b ↦ OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence e hψ.contDiffAt b) hu hv hz
  simpa only [OAI.LinearAlgebra.Moore.mooreCofactor_pairing n _ _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hv.contDiffAt)] using h

theorem moore_cofactor_energy_bounded {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x))
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have h := moore_cofactor_green_bounded e hS hb hnull hψ (hu.of_le (by norm_num)) hu hz
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

theorem moore_cofactor_energy_bounded_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)).PosSemidef) :
    0 ≤ ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [moore_cofactor_energy_bounded e hS hb hnull hψ hu hz]
  apply setIntegral_nonneg hS.measurableSet
  intro x hx
  exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)).mp
    (OAI.LinearAlgebra.Moore.mooreCofactor_posSemidef _ (hpos x hx)) _

end OAI.Analysis.PDE.Green
