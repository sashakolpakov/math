import OAI.Analysis.PDE.Elliptic.Boundary.SlopeScaling
import OAI.Analysis.PDE.Elliptic.Boundary.Quotient
import OAI.Analysis.PDE.Elliptic.Evans.HolderDecay

/-! Boundary Hölder decay of the actual quotient u(x)/height(x).
The estimate follows from the proved PDE slope contraction at every scale. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

theorem boundary_quotient_holder_oscillation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ r : ℝ, 0 < r → r ≤ 1 → boundarySlopeOsc v u r ≤ C * r ^ α := by
  obtain ⟨ρ, θ, D, hρ, hρ1, ht, ht1, hD, hstep⟩ := boundary_slope_contraction_scaled (ι := ι) hlam hL
  obtain ⟨α, hα, hα1, hholder⟩ := holder_decay_of_oscillation_contraction hρ hρ1
    (by linarith : 0 ≤ 1 - θ) (by linarith : 1 - θ < 1)
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hmM hK
  obtain ⟨C, hC, hCbound⟩ := hholder (M - m) (D * K) (sub_nonneg.mpr hmM) (mul_nonneg hD.le hK)
  refine ⟨C, hC, ?_⟩
  intro v hv A u hu hbound hlo hhi hLu
  have hb (r : ℝ) (hr1 : r ≤ 1) : ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x :=
    fun x hx htx => hbound x ⟨hx.trans hr1, htx⟩
  apply hCbound (boundarySlopeOsc v u)
  · have hh := boundarySlope_extrema_bounds v hv u (by norm_num : (0 : ℝ) < 1) (hb 1 le_rfl)
    dsimp [boundarySlopeOsc]
    linarith [hh.1, hh.2.2]
  · intro r s hr hrs hs1
    exact boundarySlopeOsc_mono v hv u hr hrs (hb s hs1)
  · intro r hr hr1
    have hext := boundarySlope_extrema_bounds v hv u hr (hb r hr1)
    obtain ⟨m', M', _, _, _, hwidth, hnew⟩ := hstep v hv r K
      (boundarySlopeInf v u r) (boundarySlopeSup v u r) hr hK hext.2.1 A u hu
      (boundarySlope_pointwise_bounds v u (hb r hr1))
      (fun x hx ht => hlo x ⟨hx.trans hr1, ht⟩)
      (fun x hx ht => hhi x ⟨hx.trans hr1, ht⟩)
      (fun x hx ht => hLu x ⟨hx.trans_le hr1, ht⟩)
    have hext' := boundarySlope_extrema_bounds v hv u (mul_pos hρ hr) hnew
    dsimp [boundarySlopeOsc] at *
    nlinarith [hext'.1, hext'.2.2]

end OAI.Analysis.PDE.Elliptic
