import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactFiber
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PartialSmoothJets
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Local Parametric Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricJets.CM

noncomputable section

/-! ThetaCycle: local smooth parameter formulas imply uniform convergence of
every real derivative on compact sets. This supports descent through fixed
local covering sections without assuming continuity of a descent operator. -/

open Set Filter
open scoped _root_.Topology ContDiff

theorem locally_parametric_uniform_derivatives
    {P E F A : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter A} (p : A → P) (p₀ : P) (hp : Tendsto p l (𝓝 p₀))
    (f : A → E → F) (f₀ : E → F) (S : Set E)
    (hlocal : ∀ x ∈ S, ∃ (U : Set E), IsOpen U ∧ x ∈ U ∧
      ∃ g : P → E → F,
        (∀ y ∈ U, ContDiffAt ℝ ∞ (Function.uncurry g) (p₀, y)) ∧
        (∀ᶠ a in l, ∀ y ∈ U, f a y = g (p a) y) ∧
        (∀ y ∈ U, f₀ y = g p₀ y))
    (m : ℕ) (K : Set E) (hK : IsCompact K) (hKS : K ⊆ S) :
    TendstoUniformlyOn (fun a => iteratedFDeriv ℝ m (f a)) (iteratedFDeriv ℝ m f₀) l K := by
  have hloc : TendstoLocallyUniformlyOn
      (fun a => iteratedFDeriv ℝ m (f a)) (iteratedFDeriv ℝ m f₀) l S := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro x hx
    obtain ⟨U, hU, hxU, g, hg, hfg, h₀⟩ := hlocal x hx
    obtain ⟨C, ⟨hCx, hC⟩, hCU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hxU)
    have hlim := CompactFiber.CM.compact_fiber_uniform_limit p p₀ hp
      (fun q y => iteratedFDeriv ℝ m (g q) y) C hC
      (fun y hy => (PartialSmoothJets.CM.partial_iteratedFDeriv_smoothAt (hg y (hCU hy)) m).continuousAt)
    have hn : ∀ᶠ a in l, ∀ y ∈ C, iteratedFDeriv ℝ m (g (p a)) y = iteratedFDeriv ℝ m (f a) y := by
      filter_upwards [hfg] with a ha
      intro y hy
      have he : g (p a) =ᶠ[𝓝 y] f a := by
        filter_upwards [hU.mem_nhds (hCU hy)] with z hz
        exact (ha z hz).symm
      exact (he.iteratedFDeriv ℝ m).eq_of_nhds
    have hz : ∀ y ∈ C, iteratedFDeriv ℝ m (g p₀) y = iteratedFDeriv ℝ m f₀ y := by
      intro y hy
      have he : g p₀ =ᶠ[𝓝 y] f₀ := by
        filter_upwards [hU.mem_nhds (hCU hy)] with z hz
        exact (h₀ z hz).symm
      exact (he.iteratedFDeriv ℝ m).eq_of_nhds
    exact ⟨C, nhdsWithin_le_nhds hCx, (hlim.congr hn).congr_right hz⟩
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hloc.mono hKS)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalParametricJets.CM
