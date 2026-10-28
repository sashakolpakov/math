import OAI.Analysis.PDE.Green.ParameterExtension
import OAI.Analysis.PDE.Green.Physical.Change

/-! Joint-in-time smooth localization of the rational physical defining
function on any compact set of admissible complex times. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter OAI.Analysis.Calculus.Current
open scoped Topology ContDiff

theorem contDiff_physicalEmbedding_joint (d : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2) := by
  apply ContDiff.add ((OAI.Analysis.Calculus.Current.physicalLift d).contDiff.comp contDiff_snd)
  apply contDiff_pi.mpr
  intro b
  cases b with
  | none =>
    change ContDiff ℝ k (fun p : ℂ × (Option (Fin d) → ℂ) => (Real.sqrt 2)⁻¹ • p.1)
    exact contDiff_fst.const_smul _
  | some b =>
    cases b with
    | none =>
      change ContDiff ℝ k (fun p : ℂ × (Option (Fin d) → ℂ) => -(Real.sqrt 2)⁻¹ • p.1)
      exact contDiff_fst.const_smul _
    | some i => exact contDiff_const

def physicalJointSublevel {d : ℕ} (a : ℝ) (T : Set ℂ) :
    Set (ℂ × (Option (Fin d) → ℂ)) :=
  {p | p.1 ∈ T ∧ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2 ≤ 0}

theorem isCompact_physicalJointSublevel {d : ℕ} (a : ℝ) (ha : 0 < a)
    {T : Set ℂ} (hT : IsCompact T) (ht : ∀ τ ∈ T, a ≤ ‖τ‖) :
    IsCompact (physicalJointSublevel (d := d) a T) := by
  let f : (ℂ × (Option (Fin d) → ℂ)) → (ℂ × (Option (Fin d) → ℂ)) :=
    fun p => (p.1, OAI.Analysis.Calculus.Current.physicalFiberInverse a p.1 p.2)
  have hf : ContinuousOn f (T ×ˢ OAI.Analysis.Calculus.Current.fiberParameterBall d) := by
    intro p hp
    exact (continuousAt_fst.prodMk
      (OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a p.1 p.2
        (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hp.2)).continuousAt).continuousWithinAt
  have heq : f '' (T ×ˢ OAI.Analysis.Calculus.Current.fiberParameterBall d) = physicalJointSublevel a T := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨hq.1, ?_⟩
      have hm : OAI.Analysis.Calculus.Current.physicalFiberInverse a q.1 q.2 ∈
          OAI.Analysis.Calculus.Current.physicalFiberInverse a q.1 '' OAI.Analysis.Calculus.Current.fiberParameterBall d := ⟨q.2, hq.2, rfl⟩
      rw [physicalFiberInverse_image_closed_ball a q.1 ha (ht q.1 hq.1)] at hm
      exact hm
    · rintro ⟨hp, hq⟩
      have hm : p.2 ∈ OAI.Analysis.Calculus.Current.physicalFiberInverse a p.1 '' OAI.Analysis.Calculus.Current.fiberParameterBall d := by
        rw [physicalFiberInverse_image_closed_ball a p.1 ha (ht p.1 hp)]
        exact hq
      obtain ⟨u, hu, he⟩ := hm
      exact ⟨(p.1, u), ⟨hp, hu⟩, Prod.ext rfl he⟩
  rw [← heq]
  exact (hT.prod (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d)).image_of_continuousOn hf

def physicalJointRegularDomain (d : ℕ) : Set (ℂ × (Option (Fin d) → ℂ)) :=
  {p | OAI.Analysis.Calculus.Current.physicalEmbedding p.1 p.2 none ≠ 0}

theorem isOpen_physicalJointRegularDomain (d : ℕ) :
    IsOpen (physicalJointRegularDomain d) :=
  isOpen_ne.preimage ((continuous_apply none).comp (contDiff_physicalEmbedding_joint d 0).continuous)

theorem contDiffOn_physicalJointDefining (d : ℕ) (a : ℝ) :
    ContDiffOn ℝ 3
      (fun p : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2)
      (physicalJointRegularDomain d) := by
  intro p hp
  exact (((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a _ hp).of_le (by norm_num)).comp p
    (contDiff_physicalEmbedding_joint d 3).contDiffAt).contDiffWithinAt

theorem physicalJointDefining_regular_boundary {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q = 0) :
    fderiv ℝ (fun p : ℂ × (Option (Fin d) → ℂ) =>
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2) (τ, q) ≠ 0 := by
  have hd := (((OAI.Analysis.Calculus.Current.contDiffAt_fiberDefining (1 / 10) a _ hY).of_le (by norm_num) :
      ContDiffAt ℝ 1 (OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)).comp (τ, q)
        (contDiff_physicalEmbedding_joint d 1).contDiffAt).differentiableAt (by norm_num)
  have hi : HasFDerivAt (fun p : Option (Fin d) → ℂ => (τ, p))
      ((0 : (Option (Fin d) → ℂ) →L[ℝ] ℂ).prod
        (ContinuousLinearMap.id ℝ (Option (Fin d) → ℂ))) q :=
    (hasFDerivAt_const τ q).prodMk (hasFDerivAt_id q)
  have hcomp := hd.hasFDerivAt.comp q hi
  intro hz
  apply OAI.Analysis.Calculus.Current.physicalFiberDefining_regular_boundary a τ q hY hr
  have heq : fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ) q =
      (fderiv ℝ (fun p : ℂ × (Option (Fin d) → ℂ) =>
        OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2) (τ, q)).comp
        ((0 : (Option (Fin d) → ℂ) →L[ℝ] ℂ).prod
          (ContinuousLinearMap.id ℝ (Option (Fin d) → ℂ))) := hcomp.fderiv
  simpa only [hz, ContinuousLinearMap.zero_comp] using heq

theorem exists_physical_joint_extension {d : ℕ} (a : ℝ) (ha : 0 < a)
    {T : Set ℂ} (hT : IsCompact T) (ht : ∀ τ ∈ T, a ≤ ‖τ‖) :
    ∃ R : (ℂ × (Option (Fin d) → ℂ)) → ℝ, ContDiff ℝ 3 R ∧
      (∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2)) ∧
      (∀ τ ∈ T, ∀ q, R (τ, q) < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ τ ∈ T, ∀ q, R (τ, q) ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) := by
  have hKU : physicalJointSublevel (d := d) a T ⊆ physicalJointRegularDomain d := by
    intro p hp
    exact (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a p.1 ha (ht p.1 hp.1)
      (hp.2.trans (by norm_num))).1
  obtain ⟨R, hR, hg, hn, hnn, _⟩ := exists_active_sublevel_extension
    (S := {p : ℂ × (Option (Fin d) → ℂ) | p.1 ∈ T})
    (isCompact_physicalJointSublevel a ha hT ht)
    (isOpen_physicalJointRegularDomain d) hKU (contDiffOn_physicalJointDefining d a)
    (fun p hp hq => ⟨hp, hq⟩)
  exact ⟨R, hR, fun τ hτ q hq => hg (τ, q) hτ hq,
    fun τ hτ q => hn (τ, q) hτ, fun τ hτ q => hnn (τ, q) hτ⟩

theorem exists_physical_joint_regular_extension {d : ℕ} (a : ℝ) (ha : 0 < a)
    {T : Set ℂ} (hT : IsCompact T) (ht : ∀ τ ∈ T, a ≤ ‖τ‖) :
    ∃ R : (ℂ × (Option (Fin d) → ℂ)) → ℝ, ContDiff ℝ 3 R ∧
      (∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2)) ∧
      (∀ τ ∈ T, ∀ q, R (τ, q) < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ τ ∈ T, ∀ q, R (τ, q) ≤ 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) ∧
      (∀ τ ∈ T, ∀ q, R (τ, q) = 0 → fderiv ℝ R (τ, q) ≠ 0) := by
  obtain ⟨R, hR, hg, hn, hnn⟩ := exists_physical_joint_extension (d := d) a ha hT ht
  refine ⟨R, hR, hg, hn, hnn, ?_⟩
  intro τ hτ q hq
  have hraw := (hnn τ hτ q).mp hq.le
  have heq := hg τ hτ q hraw
  rw [heq.fderiv_eq]
  exact physicalJointDefining_regular_boundary a τ q
    (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha (ht τ hτ)
      (hraw.trans (by norm_num))).1 (heq.eq_of_nhds.symm.trans hq)

end OAI.Analysis.PDE.Green
