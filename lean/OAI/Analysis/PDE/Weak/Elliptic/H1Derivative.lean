import OAI.Analysis.PDE.Weak.Elliptic.H1Subspace
import OAI.Analysis.PDE.Weak.Elliptic.SubspaceCompactness
import OAI.Analysis.PDE.Weak.Elliptic.Derivative
import OAI.Analysis.PDE.Weak.Boundary.H1Translation

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Difference quotients bounded in the actual H¹ graph have a derivative
which remains in the same zero-boundary graph closure. Both components are
identified by integration against compactly supported test functions. -/
theorem exists_H1_derivative_of_difference_bounds
    (p : H1Pair m) (hp0 : Integrable (p.1 : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ))
    (hp1 : Integrable (p.2 : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m))
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0)
    (hadm : ∀ n, differenceH1Pair v (s n) p ∈ H1Zero Ω)
    {C0 C1 : ℝ}
    (h0 : ∀ n, ‖differenceQuotientL2 volume v (s n) p.1‖ ≤ C0)
    (h1 : ∀ n, ‖differenceQuotientL2 volume v (s n) p.2‖ ≤ C1) :
    ∃ q : H1Pair m, q ∈ H1Zero Ω ∧
      HasWeakDirectionalDerivative volume v p.1 q.1 ∧
      HasWeakDirectionalDerivative volume v p.2 q.2 := by
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m) := FiniteDimensional.complete ℝ _
  let e : H1Hilbert m ≃L[ℝ] H1Pair m := h1HilbertEquiv
  let u : ℕ → H1Hilbert m := fun n ↦ e.symm (differenceH1Pair v (s n) p)
  have hu (n : ℕ) : u n ∈ h1ZeroHilbertSubmodule Ω := by
    change e (e.symm (differenceH1Pair v (s n) p)) ∈ h1ZeroSubmodule Ω
    rw [e.apply_symm_apply]
    exact hadm n
  have hb (n : ℕ) : ‖u n‖ ≤ ‖e.symm.toContinuousLinearMap‖ * max C0 C1 := by
    refine (e.symm.toContinuousLinearMap.le_opNorm _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    change max ‖differenceQuotientL2 volume v (s n) p.1‖
      ‖differenceQuotientL2 volume v (s n) p.2‖ ≤ max C0 C1
    exact max_le_max (h0 n) (h1 n)
  obtain ⟨g, hg, -, hlimit⟩ := exists_weak_limit_in_submodule
    (h1ZeroHilbertSubmodule Ω) (isClosed_h1ZeroHilbertSubmodule Ω) u hu hb
  refine ⟨e g, hg, ?_, ?_⟩
  · apply hasWeakDerivative_of_difference_limits volume p.1 (e g).1 hp0 v hs hs0
    intro w l hl
    let φ : H1Hilbert m →L[ℝ] ℝ := (innerSL ℝ w).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp e.toContinuousLinearMap)
    have hφ (n : ℕ) : φ (u n) = inner ℝ (differenceQuotientL2 volume v (s n) p.1) w := by
      change inner ℝ w (e (e.symm (differenceH1Pair v (s n) p))).1 = _
      rw [e.apply_symm_apply]
      exact real_inner_comm _ _
    have he := hlimit φ l (by simpa only [hφ] using hl)
    change inner ℝ w (e g).1 = l at he
    simpa only [real_inner_comm] using he
  · apply hasWeakDerivative_of_difference_limits volume p.2 (e g).2 hp1 v hs hs0
    intro w l hl
    let φ : H1Hilbert m →L[ℝ] ℝ := (innerSL ℝ w).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp e.toContinuousLinearMap)
    have hφ (n : ℕ) : φ (u n) = inner ℝ (differenceQuotientL2 volume v (s n) p.2) w := by
      change inner ℝ w (e (e.symm (differenceH1Pair v (s n) p))).2 = _
      rw [e.apply_symm_apply]
      exact real_inner_comm _ _
    have he := hlimit φ l (by simpa only [hφ] using hl)
    change inner ℝ w (e g).2 = l at he
    simpa only [real_inner_comm] using he

end OAI.Analysis.PDE.Weak
