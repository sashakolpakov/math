import OAI.Analysis.PDE.Weak.Elliptic.Difference
import OAI.Analysis.PDE.Variational.CellL2

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem integral_differenceQuotient_inner (μ : Measure X) [μ.IsAddRightInvariant]
    (v : X) (h : ℝ) (U Φ : X → V)
    (hzero : Integrable (fun x ↦ inner ℝ (U x) (Φ x)) μ)
    (hshift : Integrable (fun x ↦ inner ℝ (U (x + h • v)) (Φ x)) μ) :
    (∫ x, inner ℝ (differenceQuotient v h U x) (Φ x) ∂μ) =
      -(∫ x, inner ℝ (U x) (differenceQuotient v (-h) Φ x) ∂μ) := by
  have hback : Integrable (fun x ↦ inner ℝ (U x) (Φ (x - h • v))) μ := by
    have ht := hshift.comp_add_right (-(h • v))
    simpa only [neg_add_cancel_right, sub_eq_add_neg] using ht
  have htrans : (∫ x, inner ℝ (U (x + h • v)) (Φ x) ∂μ) =
      ∫ x, inner ℝ (U x) (Φ (x - h • v)) ∂μ := by
    simpa only [add_sub_cancel_right] using
      (integral_add_right_eq_self (fun x ↦ inner ℝ (U x) (Φ (x - h • v)))
        (h • v) (μ := μ))
  have heq : (fun x ↦ inner ℝ (U x) (differenceQuotient v (-h) Φ x)) =
      fun x ↦ -(h⁻¹) * (inner ℝ (U x) (Φ (x - h • v)) - inner ℝ (U x) (Φ x)) := by
    funext x
    simp only [differenceQuotient, inv_neg, neg_smul, real_inner_smul_right,
      sub_eq_add_neg, inner_neg_right, inner_add_right]
    ring
  simp only [differenceQuotient, real_inner_smul_left, inner_sub_left]
  rw [integral_const_mul, integral_sub hshift hzero, htrans]
  change _ = -(∫ x, inner ℝ (U x) (differenceQuotient v (-h) Φ x) ∂μ)
  rw [heq, integral_const_mul, integral_sub hback hzero]
  ring

open OAI.Analysis.PDE.Variational
variable {m : ℕ}

theorem cellGradient_differenceQuotient (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : Differentiable ℝ u) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (differenceQuotient v h u) x =
      differenceQuotient v h (OAI.Analysis.PDE.Variational.cellGradient u) x := by
  ext i
  exact fderiv_differenceQuotient v h hu x (Pi.single i 1)

theorem cellGradient_cutoff_square {η u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : Differentiable ℝ η) (hu : Differentiable ℝ u) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (fun y ↦ η y ^ 2 * u y) x =
      η x ^ 2 • OAI.Analysis.PDE.Variational.cellGradient u x + (2 * η x * u x) • OAI.Analysis.PDE.Variational.cellGradient η x := by
  ext i
  change fderiv ℝ ((fun y ↦ η y ^ 2) * u) x (Pi.single i 1) = _
  rw [(((hη x).hasFDerivAt.pow 2).mul (hu x).hasFDerivAt).fderiv]
  simp
  ring

/-- The exact translated weak equation against an actual differentiable
test. It is the starting point of the interior difference-quotient estimate. -/
theorem shifted_weak_equation (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (f w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hw : Differentiable ℝ w)
    (hzero : Integrable (fun x ↦ inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient w x)))
    (hshift : Integrable (fun x ↦ inner ℝ (H (x + h • v)) (OAI.Analysis.PDE.Variational.cellGradient w x)))
    (hweak : (∫ x, inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient (differenceQuotient v (-h) w) x)) =
      ∫ x, f x * differenceQuotient v (-h) w x) :
    (∫ x, inner ℝ (differenceQuotient v h H x) (OAI.Analysis.PDE.Variational.cellGradient w x)) =
      -(∫ x, f x * differenceQuotient v (-h) w x) := by
  rw [integral_differenceQuotient_inner volume v h H (OAI.Analysis.PDE.Variational.cellGradient w) hzero hshift]
  simp_rw [← cellGradient_differenceQuotient v (-h) hw]
  rw [hweak]

end OAI.Analysis.PDE.Weak
