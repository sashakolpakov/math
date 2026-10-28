import OAI.Analysis.Fourier.Restriction.Lattice

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def latticePhaseSum {n : ℕ} (E : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) : Space n → ℂ :=
  fun ξ ↦ ∑ k ∈ E, a k * Complex.exp (-Complex.I * ((inner ℝ (OAI.Analysis.Fourier.WavePackets.integerVector k) ξ : ℝ) : ℂ))

theorem finitePhaseSum_integerVector {n : ℕ} (E : Finset (Fin n → ℤ))
    (a : (Fin n → ℤ) → ℂ) :
    finitePhaseSum (E.image OAI.Analysis.Fourier.WavePackets.integerVector)
      (Function.extend OAI.Analysis.Fourier.WavePackets.integerVector a (fun _ ↦ 0)) = latticePhaseSum E a := by
  classical
  funext ξ
  unfold finitePhaseSum latticePhaseSum
  rw [Finset.sum_image]
  · simp only [OAI.Analysis.Fourier.WavePackets.integerVector_injective.extend_apply]
  · intro i hi j hj hij
    exact OAI.Analysis.Fourier.WavePackets.integerVector_injective hij

theorem latticePhaseSum_bound_of_separated {n : ℕ} {p : ℝ≥0∞} {q : ℝ} {C : ℝ≥0∞}
    (hbound : ∀ E : Finset (Space n),
      (∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w) → ∀ a : Space n → ℂ,
        eLpNorm (finitePhaseSum E a) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          C * ENNReal.ofReal ((∑ z ∈ E, ‖a z‖ ^ q) ^ (1 / q)))
    (E : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (latticePhaseSum E a) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      C * ENNReal.ofReal ((∑ k ∈ E, ‖a k‖ ^ q) ^ (1 / q)) := by
  classical
  have H := hbound (E.image OAI.Analysis.Fourier.WavePackets.integerVector) (integerVector_image_separated E)
    (Function.extend OAI.Analysis.Fourier.WavePackets.integerVector a (fun _ ↦ 0))
  rw [finitePhaseSum_integerVector] at H
  have he : (∑ z ∈ E.image OAI.Analysis.Fourier.WavePackets.integerVector,
      ‖Function.extend OAI.Analysis.Fourier.WavePackets.integerVector a (fun _ ↦ 0) z‖ ^ q) =
      ∑ k ∈ E, ‖a k‖ ^ q := by
    rw [Finset.sum_image]
    · simp only [OAI.Analysis.Fourier.WavePackets.integerVector_injective.extend_apply]
    · intro i hi j hj hij
      exact OAI.Analysis.Fourier.WavePackets.integerVector_injective hij
  rwa [he] at H

end OAI.Analysis.Fourier.Restriction
