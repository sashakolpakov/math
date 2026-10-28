import OAI.Analysis.PDE.Green.Physical.Change
import OAI.Analysis.PDE.Concentration.Physical.Lipschitz

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green
open scoped ContDiff

/-- The actual change from one physical fiber to another, through the
fixed parameter ball. Real periodic coordinates are left untouched. -/
def physicalFiberTransport {d : ℕ} (a : ℝ) (τ₀ τ : ℂ) (q : Option (Fin d) → ℂ) :
    Option (Fin d) → ℂ := OAI.Analysis.Calculus.Current.physicalFiberInverse a τ (OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ₀ q)

theorem physicalFiberCoordinates_mem_parameter_ball {d : ℕ} (a : ℝ) (τ : ℂ)
    {q : Option (Fin d) → ℂ} (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d := by
  have he := OAI.Analysis.PDE.Green.physical_defining_coordinates a τ q
  change (∑ i, ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q i‖ ^ 2) ≤ (1 / 100 : ℝ)
  linarith

theorem physicalFiberTransport_defining {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {q : Option (Fin d) → ℂ}
    (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ q ≤ 0) :
    OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (physicalFiberTransport a τ₀ τ q) =
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ q := by
  have hu := physicalFiberCoordinates_mem_parameter_ball a τ₀ hq
  exact (OAI.Analysis.Calculus.Current.physical_inverse_defining a τ _ ha.ne'
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)).trans
    (OAI.Analysis.PDE.Green.physical_defining_coordinates a τ₀ q).symm

theorem physicalFiberTransport_self {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {q : Option (Fin d) → ℂ}
    (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    physicalFiberTransport a τ τ q = q := by
  have hr := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht (hq.trans (by norm_num))
  exact OAI.Analysis.Calculus.Current.physicalCoordinates_left_inverse a τ q ha.ne' hr.1 hr.2

theorem physicalFiberTransport_inverse {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖) {q : Option (Fin d) → ℂ}
    (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ q ≤ 0) :
    physicalFiberTransport a τ τ₀ (physicalFiberTransport a τ₀ τ q) = q := by
  have hu := physicalFiberCoordinates_mem_parameter_ball a τ₀ hq
  unfold physicalFiberTransport
  rw [OAI.Analysis.Calculus.Current.physicalCoordinates_right_inverse a τ _ ha.ne'
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)]
  exact physicalFiberTransport_self a τ₀ ha ht₀ hq

theorem physicalFiberTransport_bijOn_closed {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) (ht : a ≤ ‖τ‖) :
    BijOn (physicalFiberTransport (d := d) a τ₀ τ)
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ q ≤ 0}
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ _ ≤ 0
    rwa [physicalFiberTransport_defining a τ₀ τ ha ht hq]
  · intro q hq r hr he
    have hi := congrArg (physicalFiberTransport a τ τ₀) he
    simpa only [physicalFiberTransport_inverse a τ₀ τ ha ht₀ ht hq,
      physicalFiberTransport_inverse a τ₀ τ ha ht₀ ht hr] using hi
  · intro q hq
    refine ⟨physicalFiberTransport a τ τ₀ q, ?_, physicalFiberTransport_inverse a τ τ₀ ha ht ht₀ hq⟩
    change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ _ ≤ 0
    rwa [physicalFiberTransport_defining a τ τ₀ ha ht₀ hq]

theorem contDiffAt_physicalCoordinates_joint {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalFiberCoordinates a p.1 p.2)
      (τ, q) := by
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | none =>
    exact (((OAI.Analysis.Calculus.Current.contDiffAt_phi_real _ hY).of_le (by simp)).comp (τ, q)
      (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).contDiffAt).div_const _
  | some i =>
    exact ((OAI.Analysis.Calculus.Current.contDiffAt_ratio _ hY i).of_le (by simp)).comp (τ, q)
      (OAI.Analysis.PDE.Green.contDiff_physicalEmbedding_joint d ∞).contDiffAt

theorem contDiffAt_physicalFiberTransport_joint {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) {q : Option (Fin d) → ℂ}
    (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ₀ q ≤ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => physicalFiberTransport a τ₀ p.1 p.2)
      (τ, q) := by
  have hu := physicalFiberCoordinates_mem_parameter_ball a τ₀ hq
  have hr := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ₀ ha ht₀ (hq.trans (by norm_num))
  have hc := (contDiffAt_physicalCoordinates_joint a τ₀ q hr.1).comp (τ, q)
    (contDiffAt_const.prodMk contDiffAt_snd)
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a τ _ (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)).restrict_scalars ℝ).of_le (by simp)).comp
    (τ, q) (contDiffAt_fst.prodMk hc)

theorem contDiffAt_physicalFiberTransport_reverse_joint {d : ℕ} (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {q : Option (Fin d) → ℂ}
    (hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) => physicalFiberTransport a p.1 τ₀ p.2)
      (τ, q) := by
  have hu := physicalFiberCoordinates_mem_parameter_ball a τ hq
  have hr := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht (hq.trans (by norm_num))
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ₀ _ (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)).restrict_scalars ℝ).of_le (by simp)).comp
    (τ, q) (contDiffAt_physicalCoordinates_joint a τ q hr.1)

end OAI.Analysis.Fourier.WavePackets
