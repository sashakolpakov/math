import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalHolomorphicLogarithm

/-! # Continuous Logarithm Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ContinuousLogarithmSmooth.CM.Construction

noncomputable section

/-! A continuous logarithm of a holomorphic function is itself
holomorphic. Thus topological logarithmic refinements retain smoothness. -/

open Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology

theorem continuous_logarithm_contMDiff
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (f l : M → ℂ) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f)
    (hl : Continuous l) (hexp : ∀ x, Complex.exp (l x) = f x) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ l := by
  intro x
  let g : M → ℂ := fun y => (Complex.exp (l x))⁻¹ * f y
  have hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ g := contMDiff_const.mul hf
  have hgx : g x = 1 := by
    change (Complex.exp (l x))⁻¹ * f x = 1
    rw [← hexp x, inv_mul_cancel₀ (Complex.exp_ne_zero _)]
  have hlog : ContDiffAt ℂ ∞ Complex.log (g x) :=
    Complex.contDiffAt_log (hgx ▸ Complex.one_mem_slitPlane)
  have hlocal : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞
      (fun y => Complex.log (g y) + l x) x :=
    (hlog.contMDiffAt.comp x (hg x)).add contMDiffAt_const
  have hzero : (0 : ℂ) ∈ Complex.expOpenPartialHomeomorph.source := by
    change -Real.pi < (0 : ℂ).im ∧ (0 : ℂ).im < Real.pi
    simpa only [Complex.zero_im, neg_lt_zero] using And.intro Real.pi_pos Real.pi_pos
  have hnear : ∀ᶠ y in 𝓝 x, l y - l x ∈ Complex.expOpenPartialHomeomorph.source := by
    have hcont : ContinuousAt (fun y => l y - l x) x := hl.continuousAt.sub continuousAt_const
    have hn := Complex.expOpenPartialHomeomorph.open_source.mem_nhds hzero
    apply hcont.eventually
    change Complex.expOpenPartialHomeomorph.source ∈ 𝓝 (l x - l x)
    simpa only [sub_self] using hn
  have heq : (fun y => Complex.log (g y) + l x) =ᶠ[𝓝 x] l := by
    filter_upwards [hnear] with y hy
    have hgy : g y = Complex.exp (l y - l x) := by
      rw [Complex.exp_sub]
      change (Complex.exp (l x))⁻¹ * f y = _
      rw [hexp y, div_eq_mul_inv, mul_comm]
    rw [hgy]
    have hlogexp : Complex.log (Complex.exp (l y - l x)) = l y - l x :=
      Complex.expOpenPartialHomeomorph.left_inv hy
    rw [hlogexp, sub_add_cancel]
  exact heq.contMDiffAt_iff.mp hlocal

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ContinuousLogarithmSmooth.CM.Construction
