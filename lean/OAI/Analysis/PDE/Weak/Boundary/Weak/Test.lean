import OAI.Analysis.PDE.Weak.Elliptic.H1

/-! Extending the actual distributional equation to all zero-trace H¹
tests, by continuity of the L² pairings and the defining graph closure. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem WeakDivergenceEquation.congr_ae
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H H' : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {f f' : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω H f) (hH : H =ᵐ[volume] H')
    (hf : f =ᵐ[volume] f') : WeakDivergenceEquation Ω H' f' := by
  intro φ hφ hs hΩ
  calc
    (∫ x, inner ℝ (H' x) (OAI.Analysis.PDE.Variational.cellGradient φ x)) =
        ∫ x, inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient φ x) := by
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      rw [hx]
    _ = ∫ x, f x * φ x := hweak φ hφ hs hΩ
    _ = ∫ x, f' x * φ x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]

theorem WeakDivergenceEquation.h1Zero_test
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    {f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hweak : WeakDivergenceEquation Ω H f) {q : H1Pair m} (hq : q ∈ H1Zero Ω) :
    inner ℝ H q.2 = inner ℝ f q.1 := by
  have hc : IsClosed {p : H1Pair m | inner ℝ H p.2 = inner ℝ f p.1} :=
    isClosed_eq (continuous_const.inner continuous_snd) (continuous_const.inner continuous_fst)
  apply closure_minimal (s := smoothH1Graph Ω) _ hc hq
  rintro p ⟨φ, hφ, hs, hΩ, rfl⟩
  change inner ℝ H (smoothH1Pair φ hφ hs).2 = inner ℝ f (smoothH1Pair φ hφ hs).1
  have hgrad : inner ℝ H (smoothH1Pair φ hφ hs).2 =
      ∫ x, inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient φ x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have ht : (smoothH1Pair φ hφ hs).2 =ᵐ[volume] OAI.Analysis.PDE.Variational.cellGradient φ :=
      ((OAI.Analysis.PDE.Variational.continuous_cellGradient (hφ.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_cellGradient hs)).coeFn_toLp
    filter_upwards [ht] with x hx
    rw [hx]
  have hval : inner ℝ f (smoothH1Pair φ hφ hs).1 = ∫ x, f x * φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have ht : (smoothH1Pair φ hφ hs).1 =ᵐ[volume] φ :=
      (hφ.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp
    filter_upwards [ht] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hgrad, hval]
  exact hweak φ hφ hs hΩ

theorem WeakDivergenceEquation.h1Zero_test_memLp
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω H f) (hH : MemLp H 2 volume) (hf : MemLp f 2 volume)
    {q : H1Pair m} (hq : q ∈ H1Zero Ω) :
    inner ℝ (hH.toLp H) q.2 = inner ℝ (hf.toLp f) q.1 := by
  exact OAI.Analysis.PDE.Weak.WeakDivergenceEquation.h1Zero_test
    (OAI.Analysis.PDE.Weak.WeakDivergenceEquation.congr_ae hweak hH.coeFn_toLp.symm hf.coeFn_toLp.symm) hq

end OAI.Analysis.PDE.Weak
