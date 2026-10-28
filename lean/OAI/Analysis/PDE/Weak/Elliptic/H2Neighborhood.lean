import OAI.Analysis.PDE.Weak.Elliptic.LocalH2
import OAI.Analysis.PDE.Weak.Elliptic.CutoffExistence

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The local H² theorem, with cutoffs constructed rather than supplied:
around every interior point all weak-gradient coordinates possess L²
weak derivatives.  Coercivity is only assumed on the equation's domain. -/
theorem interior_H2_near_point
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (p.2 x)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ j : Fin (m + 1), ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
        HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.2 g := by
  obtain ⟨θ, U, hU, hxU, hUΩ, hθ, hθs, hθsub, hθrange, hθone⟩ :=
    exists_cutoff_with_open_plateau hΩ hx
  obtain ⟨η, V, hV, hxV, hVU, hη, hηs, hηsub, hηrange, hηone⟩ :=
    exists_cutoff_with_open_plateau hU hxU
  refine ⟨V, hV, hxV, hVU.trans hUΩ, ?_⟩
  intro j
  exact local_weak_gradient_derivative A hA hlam hU hUΩ hell p hp f hweak
    θ hθ hθs hθrange hθsub hθone η hη hηs
    (fun y ↦ by rw [abs_of_nonneg (hηrange y).1]; exact (hηrange y).2)
    hηsub hηone j

end OAI.Analysis.PDE.Weak
