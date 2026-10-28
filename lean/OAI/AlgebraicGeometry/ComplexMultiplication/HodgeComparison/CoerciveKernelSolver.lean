import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveEnergy

/-! # Coercive Kernel Solver -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction

noncomputable section

section

/-! The variational energy of genuine bounded measurable L2 coefficients. -/

open _root_.MeasureTheory InnerProductSpace _root_.ContinuousLinearMap
open scoped InnerProduct

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}

def boundedFieldEnergy (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ).comp (LpCoefficients.CM.Construction.boundedFieldLp A hA hC)

theorem boundedFieldEnergy_apply (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u v : Lp E 2 μ) :
    boundedFieldEnergy A hA hC u v = ∫ x, inner ℝ (A x (u x)) (v x) ∂μ := by
  change (∫ x, inner ℝ (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u x) (v x) ∂μ) = _
  apply integral_congr_ae
  filter_upwards [LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC u] with x hx
  rw [hx]

theorem boundedFieldEnergy_integrable (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u v : Lp E 2 μ) :
    Integrable (fun x => inner ℝ (A x (u x)) (v x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u) v).congr
  filter_upwards [LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC u] with x hx
  rw [hx]

theorem boundedFieldEnergy_lower_bound (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C c : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (hc : ∀ᵐ x ∂μ, ∀ w : E, c * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w) (u : Lp E 2 μ) :
    c * ‖u‖ * ‖u‖ ≤ boundedFieldEnergy A hA hC u u := by
  have h := integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul c)
    (boundedFieldEnergy_integrable A hA hC u u) (hc.mono fun x hx => by
      simpa only [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using hx (u x))
  rw [integral_const_mul, ← L2.inner_def, real_inner_self_eq_norm_sq,
    ← boundedFieldEnergy_apply A hA hC] at h
  simpa only [pow_two, mul_assoc] using h

theorem boundedFieldEnergy_symmetric (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (hsym : ∀ᵐ x ∂μ, ∀ w z : E, inner ℝ (A x w) z = inner ℝ (A x z) w)
    (u v : Lp E 2 μ) : boundedFieldEnergy A hA hC u v = boundedFieldEnergy A hA hC v u := by
  rw [boundedFieldEnergy_apply, boundedFieldEnergy_apply]
  exact integral_congr_ae (hsym.mono fun x hx => hx (u x) (v x))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def coefficientDerivativeEnergy (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (D : V →L[ℝ] Lp E 2 μ) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V (Lp E 2 μ) ℝ).flip D).comp ((boundedFieldEnergy A hA hC).comp D)

/-- A genuine measurable positive coefficient field, composed with the actual
derivative, has a unique weak solution whenever that derivative has its
proved Poincare bound. -/
theorem coefficientDerivative_weak_existsUnique (A : α → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {C c a : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (hc : 0 < c) (ha : 0 < a)
    (hpos : ∀ᵐ x ∂μ, ∀ w : E, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (D : V →L[ℝ] Lp E 2 μ) (hD : ∀ u : V, c * ‖u‖ ≤ ‖D u‖) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, (∫ x, inner ℝ (A x (D u x)) (D v x) ∂μ) = ℓ v := by
  have hB : IsCoercive (coefficientDerivativeEnergy A hA hC D) :=
    CoerciveEnergy.CM.Construction.derivative_energy_isCoercive D _ hc ha hD (fun u => boundedFieldEnergy_lower_bound A hA hC hpos (D u))
  obtain ⟨u, hu, huniq⟩ := CoerciveEnergy.CM.Construction.coercive_energy_weak_existsUnique _ hB ℓ
  refine ⟨u, fun v => ?_, fun w hw => huniq w (fun v => ?_)⟩
  · exact (boundedFieldEnergy_apply A hA hC (D u) (D v)).symm.trans (hu v)
  · exact (boundedFieldEnergy_apply A hA hC (D w) (D v)).trans (hw v)

end

/-! A uniformly positive coefficient gives a unique normalized weak
solution on a compact graph domain, with the actual derivative kernel. -/

open _root_.MeasureTheory InnerProductSpace

variable {M H F α : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup M] [InnerProductSpace ℝ M] [CompleteSpace M]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem coefficient_graph_weak_existsUnique_orthogonal
    (J : M →L[ℝ] H) (D : M →L[ℝ] Lp F 2 μ) (hJ : IsCompactOperator J)
    (hgraph : ∀ u v, inner ℝ u v = inner ℝ (J u) (J v) + inner ℝ (D u) (D v))
    (A : α → F →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {B a : ℝ} (hB : ∀ᵐ x ∂μ, ‖A x‖ ≤ B) (ha : 0 < a)
    (hpos : ∀ᵐ x ∂μ, ∀ w : F, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (ℓ : M →L[ℝ] ℝ) (hℓ : ∀ u ∈ D.ker, ℓ u = 0) :
    ∃! u : (D.ker)ᗮ, ∀ v : M, (∫ x, inner ℝ (A x (D u.val x)) (D v x) ∂μ) = ℓ v := by
  let Q := (D.ker)ᗮ
  let JQ := J.comp Q.subtypeL
  let DQ := D.comp Q.subtypeL
  have hgraphQ : ∀ u v : Q, inner ℝ u v = inner ℝ (JQ u) (JQ v) + inner ℝ (DQ u) (DQ v) :=
    fun u v => hgraph u.val v.val
  obtain ⟨c, hc, hD⟩ := CoerciveEnergy.CM.Construction.graphEnergy_poincare_bound (𝕜 := ℝ) JQ DQ
    (hJ.comp_clm Q.subtypeL) (CompactEnergy.CM.Construction.derivative_injective_on_kernel_orthogonal D) hgraphQ
  obtain ⟨u, hu, huniq⟩ := coefficientDerivative_weak_existsUnique A hA hB hc ha hpos DQ hD (ℓ.comp Q.subtypeL)
  refine ⟨u, ?_, ?_⟩
  · intro v
    let : CompleteSpace D.ker := D.isClosed_ker.completeSpace_coe
    obtain ⟨k, hk, q, hq, rfl⟩ := D.ker.exists_add_mem_mem_orthogonal v
    have hDk : D k = 0 := hk
    have hDadd : D (k + q) = D q := by rw [map_add, hDk, zero_add]
    rw [hDadd, map_add, hℓ k hk, zero_add]
    exact hu ⟨q, hq⟩
  · intro u' hu'
    apply huniq
    intro v
    exact hu' v.val

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction
