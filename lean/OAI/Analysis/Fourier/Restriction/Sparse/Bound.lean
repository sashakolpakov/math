import OAI.Analysis.Fourier.Restriction.Sparse.FromLocal
import OAI.Analysis.Fourier.Restriction.EpsilonRemoval
import Mathlib.Data.Fintype.EquivFin

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem localSmoothing_sparseFourierBound (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      SparseFourierBound n (ENNReal.ofReal (restrictionInputExponent n)) ε (16 * n) C := by
  classical
  obtain ⟨C, hC, HC⟩ := localSmoothing_sparse_restriction_indexed hls hn hε
  refine ⟨C, hC, ?_⟩
  intro R hR T hsep f hfm hfi hfs
  let e : Fin T.card ≃ ↥T := T.equivFin.symm
  let z : Fin T.card → Space n := fun i ↦ (e i).val
  refine HC T.card R hR z ?_ f hfm hfi ?_
  · intro i j hij
    apply hsep (z i) (e i).property (z j) (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · intro x hx
    apply hfs x
    intro y hy
    have H := hx (T.equivFin ⟨y, hy⟩)
    simpa only [z, e, Equiv.symm_apply_apply] using H

/-- Euclidean local smoothing gives global diagonal restriction below the
critical input exponent, with no spatial support assumption and no loss. -/
theorem localSmoothing_global_restriction (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 1 ≤ q) (hqc : q < restrictionInputExponent n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Space n → ℂ, Integrable f →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal q) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * eLpNorm f (ENNReal.ofReal q) volume := by
  exact sparse_bound_implies_restriction hq hqc (by omega : 0 < 16 * n)
    (fun ε hε ↦ localSmoothing_sparseFourierBound hls hn hε)

end OAI.Analysis.Fourier.Restriction
