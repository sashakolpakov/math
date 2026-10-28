import OAI.Analysis.PDE.Green.MovingFiberSmooth

/-! The moving-fiber smoothness theorem needs no smooth extension through the
rational singularities or outside the closed physical fibers. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped ContDiff Topology

theorem contDiffOn_physical_fiber_integral_local {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {d : ℕ} (a : ℝ) (ha : 0 < a) (τ : E → ℂ) (hτ : ContDiff ℝ ∞ τ)
    {U : Set E} (hU : IsOpen U) (htime : ∀ x ∈ U, a ≤ ‖τ x‖)
    {O : Set (E × (Option (Fin d) → ℂ))} (hO : IsOpen O)
    (f : E × (Option (Fin d) → ℂ) → ℝ) (hf : ContDiffOn ℝ ∞ f O)
    (hcontains : ∀ x ∈ U, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (τ x) q ≤ 0 → (x, q) ∈ O) :
    ContDiffOn ℝ ∞
      (fun x => ∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (τ x) q < 0}, f (x, q)) U := by
  let T : E × (Option (Fin d) → ℂ) → ℂ × (Option (Fin d) → ℂ) :=
    fun p => (τ p.1, p.2)
  have hT : ContDiff ℝ ∞ T := (hτ.comp contDiff_fst).prodMk contDiff_snd
  let Ω₀ := T ⁻¹' physicalParameterDomain d a
  have hΩ₀ : IsOpen Ω₀ := (isOpen_physicalParameterDomain d a).preimage hT.continuous
  let J : E × (Option (Fin d) → ℂ) → E × (Option (Fin d) → ℂ) :=
    fun p => (p.1, OAI.Analysis.Calculus.Current.physicalFiberInverse a (τ p.1) p.2)
  have hJ : ContDiffOn ℝ ∞ J Ω₀ := by
    intro p hp
    have hp' : Real.sqrt 2 • τ p.1 + a • p.2 none ≠ 0 ∧
        OAI.Analysis.Calculus.Current.fiberDenominator (fun i => p.2 (some i)) ≠ 0 := hp
    have hI : ContDiffAt ℝ ∞
        (fun z : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalFiberInverse a z.1 z.2)
        (τ p.1, p.2) :=
      ((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a (τ p.1) p.2 hp'.2).restrict_scalars ℝ).of_le (by simp)
    exact (contDiffAt_fst.prodMk (hI.comp p hT.contDiffAt)).contDiffWithinAt
  have hJac : ContDiffOn ℝ ∞
      (fun p : E × (Option (Fin d) → ℂ) => |OAI.Analysis.Calculus.Current.physicalInverseJacobian a (τ p.1) p.2|) Ω₀ := by
    intro p hp
    have hp' : Real.sqrt 2 • τ p.1 + a • p.2 none ≠ 0 ∧
        OAI.Analysis.Calculus.Current.fiberDenominator (fun i => p.2 (some i)) ≠ 0 := hp
    exact ((contDiffAt_abs_physicalInverseJacobian a (τ p.1) p.2 ha.ne'
      hp'.1 hp'.2).comp p hT.contDiffAt).contDiffWithinAt
  let Ω := Ω₀ ∩ J ⁻¹' O
  have hΩ : IsOpen Ω := hJ.continuousOn.isOpen_inter_preimage hΩ₀ hO
  let g : E × (Option (Fin d) → ℂ) → ℝ := fun p =>
    |OAI.Analysis.Calculus.Current.physicalInverseJacobian a (τ p.1) p.2| * f (J p)
  have hg : ContDiffOn ℝ ∞ g Ω :=
    (hJac.mono inter_subset_left).mul
      (hf.comp (hJ.mono inter_subset_left) (fun _ hp => hp.2))
  have hdom : ∀ x ∈ U, ∀ u ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d, (x, u) ∈ Ω := by
    intro x hx u hu
    have hN := OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a (τ x) ha (htime x hx) hu
    have hD := OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu
    refine ⟨⟨hN, hD⟩, hcontains x hx (OAI.Analysis.Calculus.Current.physicalFiberInverse a (τ x) u) ?_⟩
    rw [OAI.Analysis.Calculus.Current.physical_inverse_defining a (τ x) u ha.ne' hN hD]
    change (∑ i, ‖u i‖ ^ 2) ≤ (1 / 100 : ℝ) at hu
    linarith
  have hfixed := contDiffOn_compact_setIntegral volume (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d)
    (isOpen_openFiberParameterBall d).measurableSet (openFiberParameterBall_subset d)
    (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d).measure_lt_top hU hΩ g hg hdom
  apply hfixed.congr
  intro x hx
  exact physical_fiber_integral_change a (τ x) ha (htime x hx) (fun q => f (x, q))

end OAI.Analysis.PDE.Green
