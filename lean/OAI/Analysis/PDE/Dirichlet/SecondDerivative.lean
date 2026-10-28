import OAI.Analysis.PDE.Dirichlet.CoerciveData
import OAI.LinearAlgebra.Moore.Concavity

open Filter Set
open scoped Topology ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Twice differentiating the actual quaternionic Monge–Ampère equation.
The right-hand side is the actual linearization, not an assumed elliptic
operator. Concavity supplies the sign of the quadratic first-variation term. -/
theorem mooreLinearization_second_directional_ge {n : ℕ}
    {ψ F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ)
    {Ω : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hA : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    F x * deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0 ≤
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ)
        (directionalDerivative (directionalDerivative ψ v) v) x := by
  have hψ3 : ContDiff ℝ 3 ψ := hψ.of_le (by norm_num)
  have hv3 : ContDiff ℝ 3 (directionalDerivative ψ v) :=
    contDiff_directionalDerivative hψ (by norm_num) v
  have hv2 : ContDiff ℝ 2 (directionalDerivative ψ v) := hv3.of_le (by norm_num)
  have hvv2 : ContDiff ℝ 2 (directionalDerivative (directionalDerivative ψ v) v) :=
    contDiff_directionalDerivative hv3 (by norm_num) v
  have hc : Continuous (fun t : ℝ ↦ x + t • v) := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto 0
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ Ω := ht.eventually (hΩ.mem_nhds hx)
  have hpos : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x + (0 : ℝ) • v))).PosDef := by
    simpa only [zero_smul, add_zero] using hA x hx
  have hD (i j : Fin n) :
      HasDerivAt (fun t : ℝ ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative ψ v)
        (x + t • v) i j)
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative (directionalDerivative ψ v) v) x i j) 0 := by
    simpa only [zero_smul, add_zero] using hasDerivAt_quaternionHessian_path OAI.Analysis.Calculus.Quaternion.fourSlots hv3 x v 0 i j
  have hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x + t • v))).PosDef ∧
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative ψ v) (x + t • v)).IsHermitian ∧
      ∀ i j, HasDerivAt (fun s : ℝ ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x + s • v) i j)
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative ψ v) (x + t • v) i j) t := by
    filter_upwards [hnear] with t ht
    exact ⟨hA _ ht, quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hv2.contDiffAt,
      hasDerivAt_quaternionHessian_path OAI.Analysis.Calculus.Quaternion.fourSlots hψ3 x v t⟩
  have hb := OAI.LinearAlgebra.Moore.mooreDifferential_second_derivative_bound
    (fun t : ℝ ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x + t • v))
    (fun t : ℝ ↦ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative ψ v) (x + t • v))
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (directionalDerivative (directionalDerivative ψ v) v) x) 0
    hpos (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hv2.contDiffAt)
    (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hvv2.contDiffAt)
    (hasDerivAt_quaternionHessian_path OAI.Analysis.Calculus.Quaternion.fourSlots hψ3 x v 0) hD hlocal
  have hlog : (fun t : ℝ ↦ Real.log (OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (x + t • v))))
      =ᶠ[𝓝 0] (fun t : ℝ ↦ Real.log (F (x + t • v))) := by
    filter_upwards [hnear] with t ht
    rw [heq _ ht]
  rw [hlog.deriv.deriv_eq] at hb
  simpa only [zero_smul, add_zero, heq x hx, mooreLinearization] using hb

/-- The interior pure-second-derivative estimate, with its boundary input
explicit. The forcing is the prescribed logarithmic density along lines. -/
theorem quaternionic_second_directional_estimate_of_barrier_coercivity {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {κ L B : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (hcoercive : ∀ x ∈ interior K, κ ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x)
    (hdata : ∀ x ∈ interior K,
      -L ≤ F x * deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K →
      directionalDerivative (directionalDerivative ψ v) v x ≤ B)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, directionalDerivative (directionalDerivative ψ v) v x ≤ B - (L / κ) * r x := by
  have hv3 : ContDiff ℝ 3 (directionalDerivative ψ v) :=
    contDiff_directionalDerivative hψ (by norm_num) v
  have hvv2 : ContDiff ℝ 2 (directionalDerivative (directionalDerivative ψ v) v) :=
    contDiff_directionalDerivative hv3 (by norm_num) v
  apply moore_linearized_upper_estimate hn hK hvv2 hr hA ?_ hboundary hrbd
  intro x hx
  have hb := (hdata x hx).trans (mooreLinearization_second_directional_ge hψ isOpen_interior hA heq v hx)
  have hc := mul_le_mul_of_nonneg_left (hcoercive x hx) (div_nonneg hL hκ.le)
  rw [div_mul_cancel₀ _ hκ.ne'] at hc
  linarith

/-- Data-only form of the interior second-derivative upper estimate. No lower
bound on the eigenvalues of the unknown solution is an input. -/
theorem quaternionic_second_directional_estimate {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {m M r₀ L B : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hdataBounds : ∀ x ∈ interior K, m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x ∈ interior K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x -
        r₀ • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ x ∈ interior K,
      -L ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0)
    (hboundary : ∀ x ∈ K, x ∉ interior K →
      directionalDerivative (directionalDerivative ψ v) v x ≤ B)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, directionalDerivative (directionalDerivative ψ v) v x ≤
      B - ((L * M) / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x := by
  apply quaternionic_second_directional_estimate_of_barrier_coercivity
    hn hK hψ hr hA heq v (by positivity) (mul_nonneg hL hM) ?_ ?_ hboundary hrbd
  · intro x hx
    apply mooreDifferential_defining_lower hn _ _ (hA x hx) hr₀
    · rw [heq x hx]
      exact (hdataBounds x hx).1
    · rw [heq x hx]
      exact (hdataBounds x hx).2
    · exact hconvex x hx
  · intro x hx
    have hFx : 0 ≤ F x := (hm.trans_le (hdataBounds x hx).1).le
    have hprod := mul_le_mul_of_nonneg_left (hdata x hx) hFx
    have hLM := mul_le_mul_of_nonneg_left (hdataBounds x hx).2 hL
    nlinarith

end OAI.Analysis.PDE.Dirichlet
