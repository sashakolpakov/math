import OAI.Analysis.PDE.Green.JacobianSmooth

/-! Smooth dependence of actual moving-fiber integrals.  The fixed-domain
formula is proved by the real Jacobian change of variables, not assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped ContDiff Topology

def physicalParameterDomain (d : ℕ) (a : ℝ) : Set (ℂ × (Option (Fin d) → ℂ)) :=
  {p | Real.sqrt 2 • p.1 + a • p.2 none ≠ 0 ∧
    OAI.Analysis.Calculus.Current.fiberDenominator (fun i => p.2 (some i)) ≠ 0}

theorem isOpen_physicalParameterDomain (d : ℕ) (a : ℝ) :
    IsOpen (physicalParameterDomain d a) := by
  have hN : Continuous (fun p : ℂ × (Option (Fin d) → ℂ) =>
      Real.sqrt 2 • p.1 + a • p.2 none) := by fun_prop
  have hD : Continuous (fun p : ℂ × (Option (Fin d) → ℂ) =>
      OAI.Analysis.Calculus.Current.fiberDenominator (fun i => p.2 (some i))) := by
    unfold OAI.Analysis.Calculus.Current.fiberDenominator OAI.Analysis.Calculus.Current.fiberQuadratic
    fun_prop
  exact (isOpen_ne.preimage hN).inter (isOpen_ne.preimage hD)

theorem contDiffOn_physical_fiber_integral {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {d : ℕ} (a : ℝ) (ha : 0 < a) (τ : E → ℂ) (hτ : ContDiff ℝ ∞ τ)
    (f : E × (Option (Fin d) → ℂ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞
      (fun x => ∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (τ x) q < 0}, f (x, q))
      {x | a < ‖τ x‖} := by
  let T : E × (Option (Fin d) → ℂ) → ℂ × (Option (Fin d) → ℂ) :=
    fun p => (τ p.1, p.2)
  have hT : ContDiff ℝ ∞ T := (hτ.comp contDiff_fst).prodMk contDiff_snd
  let Ω := T ⁻¹' physicalParameterDomain d a
  have hΩ : IsOpen Ω := (isOpen_physicalParameterDomain d a).preimage hT.continuous
  have hU : IsOpen {x | a < ‖τ x‖} := isOpen_lt continuous_const hτ.continuous.norm
  let g : E × (Option (Fin d) → ℂ) → ℝ := fun p =>
    |OAI.Analysis.Calculus.Current.physicalInverseJacobian a (τ p.1) p.2| * f (p.1, OAI.Analysis.Calculus.Current.physicalFiberInverse a (τ p.1) p.2)
  have hg : ContDiffOn ℝ ∞ g Ω := by
    intro p hp
    have hp' : Real.sqrt 2 • τ p.1 + a • p.2 none ≠ 0 ∧
        OAI.Analysis.Calculus.Current.fiberDenominator (fun i => p.2 (some i)) ≠ 0 := hp
    have hJ := (contDiffAt_abs_physicalInverseJacobian a (τ p.1) p.2 ha.ne'
      hp'.1 hp'.2).comp p hT.contDiffAt
    have hI : ContDiffAt ℝ ∞
        (fun z : ℂ × (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.physicalFiberInverse a z.1 z.2)
        (τ p.1, p.2) :=
      ((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a (τ p.1) p.2 hp'.2).restrict_scalars ℝ).of_le (by simp)
    have hI' := hI.comp p hT.contDiffAt
    have hF := hf.contDiffAt.comp p (contDiffAt_fst.prodMk hI')
    exact (hJ.mul hF).contDiffWithinAt
  have hdom : ∀ x ∈ {x | a < ‖τ x‖}, ∀ u ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d, (x, u) ∈ Ω := by
    intro x hx u hu
    exact ⟨OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a (τ x) ha (le_of_lt hx) hu,
      OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu⟩
  have hfixed := contDiffOn_compact_setIntegral volume (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d)
    (isOpen_openFiberParameterBall d).measurableSet (openFiberParameterBall_subset d)
    (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d).measure_lt_top hU hΩ g hg hdom
  apply hfixed.congr
  intro x hx
  exact physical_fiber_integral_change a (τ x) ha (le_of_lt hx) (fun q => f (x, q))

end OAI.Analysis.PDE.Green
