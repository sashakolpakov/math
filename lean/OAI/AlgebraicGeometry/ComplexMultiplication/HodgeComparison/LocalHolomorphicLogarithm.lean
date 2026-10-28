import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Local Holomorphic Logarithm -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalHolomorphicLogarithm.CM.Construction

noncomputable section

/-! Nonvanishing holomorphic functions admit actual holomorphic
logarithms on explicitly chosen neighborhoods. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem exists_local_holomorphic_logarithm
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (f : M → ℂ) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f)
    (x : M) (hx : f x ≠ 0) :
    ∃ U : Opens M, x ∈ U ∧ ∃ l : U → ℂ,
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ l ∧ ∀ y : U, Complex.exp (l y) = f y.val := by
  let g : M → ℂ := fun y => (f x)⁻¹ * f y
  have hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ g := contMDiff_const.mul hf
  let U : Opens M := ⟨g ⁻¹' Complex.slitPlane, Complex.isOpen_slitPlane.preimage hg.continuous⟩
  have hxU : x ∈ U := by
    change (f x)⁻¹ * f x ∈ Complex.slitPlane
    rw [inv_mul_cancel₀ hx]
    exact Complex.one_mem_slitPlane
  let l : U → ℂ := fun y => Complex.log (g y.val) + Complex.log (f x)
  refine ⟨U, hxU, l, ?_, ?_⟩
  · intro y
    have hlog : ContDiffAt ℂ ∞ Complex.log (g y.val) := Complex.contDiffAt_log y.property
    exact (hlog.contMDiffAt.comp y
      ((hg y.val).comp y (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞) y))).add contMDiffAt_const
  · intro y
    have hy : g y.val ≠ 0 := Complex.slitPlane_ne_zero y.property
    change Complex.exp (Complex.log (g y.val) + Complex.log (f x)) = _
    rw [Complex.exp_add, Complex.exp_log hy, Complex.exp_log hx]
    dsimp only [g]
    field_simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalHolomorphicLogarithm.CM.Construction
