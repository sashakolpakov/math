import OAI.Analysis.PDE.Weak.Boundary.Halfspace.LocalSmooth
import OAI.Analysis.PDE.Weak.Boundary.LocalFamily

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A genuine weak halfspace solution with smooth data supplies a complete
compactly supported derivative family, ready for finite reflection. -/
theorem halfspace_smooth_derivative_family
    (k : Fin (m + 1)) (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    (N : ℕ) {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    (hell : ∀ x ∈ U, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < x k})
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ x ∂volume, x ∈ {x | 0 < x k} ∩ U → f x = g x)
    (he : WeakDivergenceEquation ({x | 0 < x k} ∩ U) (fun x => A x (p.2 x)) f)
    {x₀ : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx₀ : x₀ ∈ U) :
    ∃ (V K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m))
      (F : List (Fin (m + 1)) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))),
      IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ᵐ y ∂volume, y ∈ V → F [] y = p.1 y) ∧
      (∀ α, α.length ≤ N + 2 → ∀ᵐ y ∂volume, y ∉ K → F α y = 0) ∧
      (∀ α, α.length < N + 2 → ∀ i,
        HasWeakDirectionalDerivativeOn volume {x | 0 < x k} (Pi.single i 1) (F α) (F (i :: α))) := by
  obtain ⟨W, hW, hxW, hWU, _, hr⟩ := halfspace_local_smooth_regular_near_point
    k A hA hlam N hU hell p hp f g hg hfg he hx₀
  obtain ⟨V, K, F, hV, hxV, hVW, hK, hKW, hF, hs, hd⟩ :=
    weakRegularity_local_family_on hW hxW hr
  exact ⟨V, K, F, hV, hxV, hVW.trans hWU, hK, hKW.trans hWU, hF, hs, hd⟩

end OAI.Analysis.PDE.Weak
