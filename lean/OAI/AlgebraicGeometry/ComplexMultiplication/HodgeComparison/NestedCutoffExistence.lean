import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyInteriorRegularity
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Nested Cutoff Existence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

noncomputable section

/-! Compactly supported real smooth cutoffs equal to one on a neighborhood
of an arbitrary compact subset of an open coordinate domain. -/

open Set Filter
open scoped SchwartzMap _root_.Topology ContDiff _root_.Manifold

theorem exists_real_schwartz_cutoff_near_compact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) ∧ tsupport g ⊆ U ∧
      (∀ x, g x = Complex.ofReal (g x).re) ∧ ∀ x ∈ K, (g : E → ℂ) =ᶠ[𝓝 x] 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηnear, hηout, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hK.isClosed hKL (n := ⊤)
  have hηc : HasCompactSupport (η : E → ℝ) := HasCompactSupport.intro hL hηout
  have hηℂc : HasCompactSupport (fun x => Complex.ofReal (η x)) :=
    hηc.comp_left (show Complex.ofReal 0 = 0 from rfl)
  have hηℂ : ContDiff ℝ ∞ (fun x => Complex.ofReal (η x)) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
      (E := ℝ) (F := ℂ) Complex.ofRealCLM).comp η.contMDiff.contDiff
  let g : 𝓢(E, ℂ) := hηℂc.toSchwartzMap hηℂ
  have hs : Function.support (g : E → ℂ) ⊆ L := by
    intro x hx
    by_contra hn
    apply hx
    change Complex.ofReal (η x) = 0
    rw [hηout x hn, Complex.ofReal_zero]
  refine ⟨g, hηℂc, (closure_minimal hs hL.isClosed).trans hLU, ?_, ?_⟩
  · intro x
    change Complex.ofReal (η x) = Complex.ofReal (Complex.ofReal (η x)).re
    rw [Complex.ofReal_re]
  · intro x hx
    have hn : ∀ᶠ y in 𝓝 x, η y = 1 := (nhds_le_nhdsSet hx) hηnear
    filter_upwards [hn] with y hy
    change Complex.ofReal (η y) = 1
    rw [hy, Complex.ofReal_one]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction
