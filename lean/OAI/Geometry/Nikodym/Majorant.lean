import OAI.Geometry.Nikodym.PieceCover

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def slopeBound (d : ℕ) : ℝ := (d:ℝ)+2
def nearFactor (d : ℕ) : ℝ := 1+2*stripDilation (slopeBound d)*slopeBound d

def tubeMajorant {d : ℕ} (δ : ℝ) (N : ℕ) (f : Space (d+1) → ℂ)
    (x : Space (d+1)) : ℝ≥0∞ :=
  ∑ i : Fin (d+1), ∑ k : Option (Fin N × Bool),
    pieceBound δ (stripDilation (slopeBound d)*δ) (nearFactor d) (slopeBound d)
      (coordinateSwap i) f k x

theorem measurable_tubeMajorant {d : ℕ} (δ : ℝ) (N : ℕ)
    {f : Space (d+1) → ℂ} (hf : Measurable f) : Measurable (tubeMajorant δ N f) := by
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
    measurable_pieceBound _ _ _ _ _ hf k

theorem exists_tubeMajorant_mass_bound {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (f : Space (d+1) → ℂ), Measurable f →
      ∀ (ω a x : Space (d+1)), ‖ω‖ = 1 → x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a →
        (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω a, ‖f y‖ₑ) / ENNReal.ofReal (δ^d) ≤ tubeMajorant δ N f x := by
  have hV : 0 ≤ slopeBound d := by unfold slopeBound; positivity
  have hD : 0 < stripDilation (slopeBound d) := by unfold stripDilation; positivity
  obtain ⟨N,_,hN⟩ := exists_finite_coordinate_tube_decomposition (mul_pos hD hδ) δ
  refine ⟨N,?_⟩
  intro f hf ω a x hω hx
  obtain ⟨i,hv,hcover⟩ := hN ω a x hω hx
  have hc : ∀ y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a, ∃ k : Option (Fin N × Bool),
      y ∈ pieceSet δ (stripDilation (slopeBound d)*δ) (nearFactor d)
        (coordinateSwap i) x (directionSlope (coordinateSwap i ω)) k := by
    intro y hy
    rcases hcover y hy with hn | ⟨j,hj,hr,hp | hm⟩
    · refine ⟨none,?_⟩
      change y ∈ ball x (nearFactor d*δ)
      convert hn using 2 ; unfold nearFactor slopeBound ; ring
    · refine ⟨some (⟨j,hj⟩,true),?_⟩
      simpa [pieceSet,hr,signedDyadicRadius] using hp
    · refine ⟨some (⟨j,hj⟩,false),?_⟩
      simpa [pieceSet,hr,signedDyadicRadius] using hm
  have h := covered_tube_average_le hδ _ _ (coordinateSwap i) x hv
    (OAI.MeasureTheory.Kakeya.isOpen_tube δ ω a).measurableSet hc hf
  apply h.trans
  exact Finset.single_le_sum
    (f := fun i => ∑ k : Option (Fin N × Bool),
      pieceBound δ (stripDilation (slopeBound d)*δ) (nearFactor d) (slopeBound d)
        (coordinateSwap i) f k x) (fun _ _ => bot_le) (Finset.mem_univ i)

end OAI.Geometry.Nikodym
