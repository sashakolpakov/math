import OAI.Analysis.PDE.Weak.Boundary.Halfspace.Regularity
import OAI.Analysis.PDE.Weak.Boundary.CoefficientBounds
import OAI.Analysis.PDE.Weak.Boundary.ValueRegularity

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Smooth coefficients which are fixed off a compact patch require no
supplied derivative bounds or inverse-regularity assumptions. -/
theorem halfspace_smooth_regular_near_point
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hK : IsCompact K)
    (A₀ : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hfixed : ∀ x ∉ K, A x = A₀)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (N : ℕ) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hf : WeakRegularity ({x | 0 < x k} ∩ U) N f)
    (he : WeakDivergenceEquation ({x | 0 < x k} ∩ U) (fun x => A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      WeakRegularity ({x | 0 < x k} ∩ V) (N + 1) p.2 ∧
      WeakRegularity ({x | 0 < x k} ∩ V) (N + 2) p.1 := by
  have hAb := smoothBounded_of_eq_const_off_compact hA hK A₀ hfixed
  obtain ⟨Λ, hΛ⟩ := hAb.bound
  obtain ⟨D, hD0, hD⟩ := exists_fderiv_bound_of_eq_const_off_compact hA hK A₀ hfixed
  have hi : SmoothBounded (fun x => (realOperatorEntry (A x) k k)⁻¹) :=
    smoothBounded_inv_of_eq_const_off_compact (contDiff_realOperatorEntry A hA k k)
      (fun x => ne_of_gt (hlam.trans_le (realOperatorEntry_diagonal_lower (A x) (hell x) k)))
      hK (realOperatorEntry A₀ k k) (fun x hx => by rw [hfixed x hx])
  obtain ⟨V, hV, hxV, hVU, hr⟩ := halfspace_regular_near_point k A hAb hi hlam
    ((norm_nonneg _).trans (hΛ 0)) hD0 hΛ hD hell N hU p hp f hf he hx₀
  exact ⟨V, hV, hxV, hVU, hr, OAI.Analysis.PDE.Weak.H1Zero.value_regular_of_gradient_regular hp hr⟩

end OAI.Analysis.PDE.Weak
