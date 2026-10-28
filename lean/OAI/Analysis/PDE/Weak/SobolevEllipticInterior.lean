import OAI.Analysis.Normed.Function.Sobolev.PiEmbedding
import OAI.Analysis.PDE.Weak.Elliptic.LocalFamily

open Set _root_.MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

/-- Interior weak-to-classical regularity at the level of representatives.
The C^q function is obtained from the actual weak equation, by weak derivative
iteration and Fourier Sobolev embedding. -/
theorem smooth_elliptic_contDiff_local_representative {m : ℕ} (q : ℕ)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ q u ∧
      (∀ᵐ y ∂volume, y ∈ V → p.1 y = u y) := by
  obtain ⟨V, K, U, hV, hxV, hVΩ, hK, _hKΩ, hU, hUs, hUd⟩ :=
    smooth_elliptic_local_derivative_family A hA hlam (m + q + 2)
      hΩ hell p hp f g hg hfg he hx
  obtain ⟨u, hu, hueq⟩ := OAI.Analysis.Normed.Function.Sobolev.exists_contDiff_pi_representative_of_compact_L2_derivatives
    (show 0 < m + 1 by omega) (show (m + 1) + q < m + q + 2 by omega) U hK hUs hUd
  refine ⟨V, u, hV, hxV, hVΩ, hu, ?_⟩
  filter_upwards [hU, hueq] with y hy hyeq
  intro hyV
  exact (hy hyV).symm.trans hyeq

theorem smooth_elliptic_C2_local_representative {m : ℕ}
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ Ω → f x = g x)
    (he : WeakDivergenceEquation Ω (fun y ↦ A y (p.2 y)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ (V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ContDiff ℝ 2 u ∧
      (∀ᵐ y ∂volume, y ∈ V → p.1 y = u y) :=
  smooth_elliptic_contDiff_local_representative 2 A hA hlam hΩ hell p hp f g hg hfg he hx

end OAI.Analysis.PDE.Weak
