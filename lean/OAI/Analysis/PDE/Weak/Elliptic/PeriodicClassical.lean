import OAI.Analysis.PDE.Weak.Elliptic.Classical.LocalSolution
import OAI.Analysis.PDE.Variational.PeriodicH1Equation

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The actual periodic variational solution has a smooth classical interior
representative. The local argument includes all fundamental-cell seams. -/
theorem periodic_weak_solution_classical_representative
    (J : Finset (Fin (m + 1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hΩ : ∀ z x, x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m + 1)) (hk : k ∉ J)
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : OAI.Analysis.PDE.Variational.PeriodicH10 a b Ω (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b - a)))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : WeakDivergenceEquation Ω
      (fun y ↦ A y (OAI.Analysis.PDE.Variational.periodicRepresentative J a b u.val y)) (OAI.Analysis.PDE.Variational.periodicRepresentative J a b f))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y ∂volume, y ∈ Ω → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y) :
    ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ ∞ v Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) y) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) := by
  apply smooth_classical_representative_of_local_weak_solution A hA hlam hopen hell
    (OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u)) g hg
  intro x hx
  obtain ⟨U, q, F, hU, hxU, hUΩ, hq, heq, hqe⟩ := OAI.Analysis.PDE.Variational.periodicRepresentative_local_H1_equation
    J a b hab hL Ω hopen htrans hΩ k hk hface u A f hweak x hx
  refine ⟨U, q, F, hU, hxU, hUΩ, hq, ?_, ?_, heq⟩
  · exact hqe.mono fun y hy hys ↦ (hy hys).1
  · filter_upwards [hqe, hfg] with y hy hz
    intro hys
    exact (hy hys).2.2.trans (hz (hUΩ hys))

end OAI.Analysis.PDE.Weak
