import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodContinuation
import Mathlib.Analysis.Normed.Module.Basic

/-! # Logarithmic Torsion Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LogarithmicTorsionRigidity.Abelian

noncomputable section

/-!
A torsion section with a continuous logarithm tending to zero is locally
the identity when the actual exponential kernels have a common gap at
zero. This is the local uniqueness step for finite level structures.
-/

open Set _root_.Metric
open scoped _root_.Topology

/-- The common relative logarithm applies to every continuous section
through the identity, using its actual total-space coordinates. -/
theorem exists_continuous_section_logarithm
    {P V X : Type} [TopologicalSpace P] [NormedAddCommGroup V] [TopologicalSpace X]
    (G : P → Type) [∀ p, Group (G p)]
    (exponential : ∀ p, V → G p)
    (embed : ∀ p, G p → X) (hembed : ∀ p, Function.Injective (embed p))
    (e : OpenPartialHomeomorph X (P × V))
    (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (δ : ℝ) (hδ : 0 < δ) (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ closedBall (0 : V) (δ / 2)))
    (hlog₀ : logarithm (p₀, 0) = 0)
    (hright : ∀ p ∈ B, ∀ y ∈ closedBall (0 : V) (δ / 2),
      embed p (exponential p (logarithm (p, y))) = e.symm (p, y))
    (hprojection : ∀ p ∈ B, ∀ z : G p, embed p z ∈ e.source →
      (e (embed p z)).1 = p)
    (hunit : embed p₀ 1 ∈ e.source) (hunit₀ : e (embed p₀ 1) = (p₀, 0))
    (z : ∀ p, G p) (hz₀ : z p₀ = 1)
    (hcont : ContinuousAt (fun p => embed p (z p)) p₀) :
    ∃ l : P → V, ContinuousAt l p₀ ∧ l p₀ = 0 ∧
      ∀ᶠ p in 𝓝 p₀, exponential p (l p) = z p := by
  let φ := fun p => embed p (z p)
  let y := fun p => (e (φ p)).2
  have hφ₀ : φ p₀ = embed p₀ 1 := congrArg (embed p₀) hz₀
  have hsource₀ : φ p₀ ∈ e.source := hφ₀ ▸ hunit
  have he₀ : e (φ p₀) = (p₀, (0 : V)) := hφ₀ ▸ hunit₀
  have hy₀ : y p₀ = 0 := congrArg Prod.snd he₀
  have hy : ContinuousAt y p₀ :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hsource₀)).comp hcont).snd
  have hs : ∀ᶠ p in 𝓝 p₀, φ p ∈ e.source :=
    hcont.preimage_mem_nhds (e.open_source.mem_nhds hsource₀)
  have hsmall : ∀ᶠ p in 𝓝 p₀, y p ∈ closedBall (0 : V) (δ / 2) := by
    apply hy.preimage_mem_nhds
    rw [hy₀]
    exact closedBall_mem_nhds _ (half_pos hδ)
  have hlogAt : ContinuousAt logarithm (p₀, y p₀) := by
    rw [hy₀]
    exact hlog.continuousAt
      (prod_mem_nhds (hB.mem_nhds hp₀) (closedBall_mem_nhds _ (half_pos hδ)))
  refine ⟨fun p => logarithm (p, y p),
    hlogAt.comp (f := fun p => (p, y p)) (continuousAt_id.prodMk hy), ?_, ?_⟩
  · change logarithm (p₀, y p₀) = 0
    rw [hy₀, hlog₀]
  · filter_upwards [hB.mem_nhds hp₀, hs, hsmall] with p hp hsp hyp
    have he : e (φ p) = (p, y p) := Prod.ext (hprojection p hp (z p) hsp) rfl
    apply hembed p
    exact (hright p hp (y p) hyp).trans (by rw [← he, e.left_inv hsp])

theorem additive_exponential_nsmul {V G : Type*} [AddMonoid V] [Monoid G]
    (exponential : V → G) (hzero : exponential 0 = 1)
    (hadd : ∀ v w, exponential (v + w) = exponential v * exponential w)
    (n : ℕ) (v : V) : exponential (n • v) = exponential v ^ n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem torsion_section_eq_one_of_continuous_logarithm
    {P V : Type} [TopologicalSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : P → Type) [∀ p, Group (G p)]
    (exponential : ∀ p, V → G p)
    (hzero : ∀ p, exponential p 0 = 1)
    (hadd : ∀ p v w, exponential p (v + w) = exponential p v * exponential p w)
    (p₀ : P) (B : Set P) (hB : B ∈ 𝓝 p₀) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ, exponential p v = 1 → v = 0)
    (z : ∀ p, G p) (logarithm : P → V)
    (hlogcont : ContinuousAt logarithm p₀) (hlogzero : logarithm p₀ = 0)
    (hlog : ∀ᶠ p in 𝓝 p₀, exponential p (logarithm p) = z p)
    (n : ℕ) (hn : 0 < n) (htorsion : ∀ᶠ p in 𝓝 p₀, z p ^ n = 1) :
    ∀ᶠ p in 𝓝 p₀, z p = 1 := by
  have hcont : ContinuousAt (fun p => (n : ℝ) • logarithm p) p₀ :=
    continuousAt_const.smul hlogcont
  have hz : (n : ℝ) • logarithm p₀ ∈ ball (0 : V) δ := by simp [hlogzero, hδ]
  have hball := hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hz)
  filter_upwards [hB, hball, hlog, htorsion] with p hp hnorm hlogp hnp
  have he : exponential p ((n : ℝ) • logarithm p) = 1 := by
    rw [Nat.cast_smul_eq_nsmul ℝ,
      additive_exponential_nsmul (exponential p) (hzero p) (hadd p), hlogp]
    exact hnp
  have hv : (n : ℝ) • logarithm p = 0 := hsmall p hp _ (ball_subset_closedBall hnorm) he
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hl : logarithm p = 0 := (smul_eq_zero.mp hv).resolve_left hn'
  exact hlogp.symm.trans ((congrArg (exponential p) hl).trans (hzero p))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LogarithmicTorsionRigidity.Abelian
