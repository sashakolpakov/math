import OAI.Geometry.Nikodym.RotatedStrip
import OAI.Geometry.Nikodym.BallAverage
import OAI.Geometry.Nikodym.FiniteCover
import OAI.Geometry.Nikodym.DyadicDecomposition

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def signedDyadicRadius (j : ℕ) (b : Bool) : ℝ :=
  if b then dyadicRadius j else -dyadicRadius j

theorem abs_signedDyadicRadius (j : ℕ) (b : Bool) :
    |signedDyadicRadius j b| = dyadicRadius j := by
  cases b <;> simp [signedDyadicRadius,abs_of_pos (dyadicRadius_pos j)]

theorem signedDyadicRadius_ne_zero (j : ℕ) (b : Bool) : signedDyadicRadius j b ≠ 0 := by
  apply abs_pos.mp
  rw [abs_signedDyadicRadius]
  exact dyadicRadius_pos j

def pieceSet {d N : ℕ} (δ ρ K : ℝ) (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1))
    (x : Space (d+1)) (v : Space d) : Option (Fin N × Bool) → Set (Space (d+1))
  | none => ball x (K*δ)
  | some (j,b) => if ρ ≤ dyadicRadius j then
      L ⁻¹' neighborhood δ (scaledLinePiece (L x) v (signedDyadicRadius j b)) else ∅

def pieceBound {d N : ℕ} (δ ρ K V : ℝ) (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1))
    (f : Space (d+1) → ℂ) : Option (Fin N × Bool) → Space (d+1) → ℝ≥0∞
  | none => ballAverage δ K f
  | some (j,b) => if ρ ≤ dyadicRadius j then rotatedStrip δ V (signedDyadicRadius j b) L f else 0

theorem measurableSet_pieceSet {d N : ℕ} (δ ρ K : ℝ)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) (x : Space (d+1)) (v : Space d)
    (k : Option (Fin N × Bool)) : MeasurableSet (pieceSet δ ρ K L x v k) := by
  cases k with
  | none => exact isOpen_ball.measurableSet
  | some k =>
    rcases k with ⟨j,b⟩
    by_cases h : ρ ≤ dyadicRadius j
    · simpa only [pieceSet,ite_eq_left h] using
        (isOpen_neighborhood δ (scaledLinePiece (L x) v (signedDyadicRadius j b))).measurableSet.preimage L.continuous.measurable
    · simp only [pieceSet,ite_eq_right h]; exact MeasurableSet.empty

theorem measurable_pieceBound {d N : ℕ} (δ ρ K V : ℝ)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) {f : Space (d+1) → ℂ} (hf : Measurable f)
    (k : Option (Fin N × Bool)) : Measurable (pieceBound δ ρ K V L f k) := by
  cases k with
  | none => exact measurable_ballAverage δ K hf
  | some k =>
    rcases k with ⟨j,b⟩
    by_cases h : ρ ≤ dyadicRadius j
    · simpa only [pieceBound,ite_eq_left h] using measurable_rotatedStrip δ V (signedDyadicRadius j b) L hf
    · simp only [pieceBound,ite_eq_right h]; exact measurable_const

theorem pieceSet_average_le {d N : ℕ} {δ V : ℝ} (hδ : 0 < δ) (ρ K : ℝ)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) (x : Space (d+1)) {v : Space d} (hv : ‖v‖ ≤ V)
    {f : Space (d+1) → ℂ} (hf : Measurable f) (k : Option (Fin N × Bool)) :
    (∫⁻ y in pieceSet δ ρ K L x v k, ‖f y‖ₑ) / ENNReal.ofReal (δ^d) ≤
      pieceBound δ ρ K V L f k x := by
  cases k with
  | none => exact le_rfl
  | some k =>
    rcases k with ⟨j,b⟩
    by_cases h : ρ ≤ dyadicRadius j
    · simpa only [pieceSet,pieceBound,ite_eq_left h] using
        rotatedStrip_average_le hδ (signedDyadicRadius_ne_zero j b) L hv hf x
    · simp [pieceSet,pieceBound,h]

theorem covered_tube_average_le {d N : ℕ} {δ V : ℝ} (hδ : 0 < δ) (ρ K : ℝ)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) (x : Space (d+1)) {v : Space d} (hv : ‖v‖ ≤ V)
    {s : Set (Space (d+1))} (hs : MeasurableSet s)
    (hcover : ∀ y ∈ s, ∃ k : Option (Fin N × Bool), y ∈ pieceSet δ ρ K L x v k)
    {f : Space (d+1) → ℂ} (hf : Measurable f) :
    (∫⁻ y in s, ‖f y‖ₑ) / ENNReal.ofReal (δ^d) ≤
      ∑ k : Option (Fin N × Bool), pieceBound δ ρ K V L f k x := by
  have h := lintegral_le_sum_of_finite_cover (μ := volume) Finset.univ hs
    (fun k _ => measurableSet_pieceSet δ ρ K L x v k) hf.enorm
    (fun y hy => by obtain ⟨k,hk⟩ := hcover y hy; exact ⟨k,Finset.mem_univ _,hk⟩)
  apply (ENNReal.div_le_div_right h _).trans
  rw [ENNReal.sum_div]
  exact Finset.sum_le_sum fun k _ => pieceSet_average_le hδ ρ K L x hv hf k

end OAI.Geometry.Nikodym
