import OAI.Analysis.PDE.Weak.Elliptic.Classical.Periodicity
import OAI.Analysis.PDE.Variational.GlobalWeakSolution

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Lax--Milgram and genuine interior regularity give a smooth periodic
classical representative of the zero-boundary variational solution. The
zero-boundary condition here is the actual closed `PeriodicH10` test space;
no pointwise boundary regularity is asserted by this interior theorem. -/
theorem exists_periodic_smooth_classical_solution
    (J : Finset (Fin (m + 1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hΩ : ∀ z x, x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m + 1)) (hk : k ∉ J)
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    {M lam : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂volume, ‖A x‖ ≤ M) (hlam : 0 < lam)
    (hell : ∀ x, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (hAp : ∀ z x, A (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z) = A x)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y ∂volume, y ∈ Ω → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y) :
    ∃ (u : OAI.Analysis.PDE.Variational.PeriodicH10 a b Ω (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b - a)))
      (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      lam * ‖u‖ ≤ (2 * (b k - a k)) * ‖f‖ ∧
      ContDiffOn ℝ ∞ v Ω ∧
      (∀ᵐ y ∂volume, y ∈ Ω → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) y) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) ∧
      (∀ (z : J → ℤ) x, x ∈ Ω → v (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b - a) z) = v x) := by
  have hmeas : AEStronglyMeasurable A (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
    hA.continuous.aestronglyMeasurable
  have hell' : ∀ᵐ x ∂volume, ∀ z : OAI.Analysis.PDE.Variational.CellVectors m,
      lam * ‖z‖ ^ 2 ≤ inner ℝ z (A x z) := by
    exact ae_of_all _ fun x z ↦ by simpa only [real_inner_comm] using hell x z
  obtain ⟨u, hweak, hbound⟩ := OAI.Analysis.PDE.Variational.exists_global_periodic_weak_solution
    J a b hab hL Ω hopen htrans hΩ k hface A hmeas hM hAM hlam hell' hAp f
  obtain ⟨v, hv, heq, hpde, hper⟩ := periodic_weak_solution_smooth_periodic
    J a b hab hL Ω hopen htrans hΩ k hk hface u A hA hlam (fun x _ ↦ hell x)
      f hweak g hg hfg
  exact ⟨u, v, hbound, hv, heq, hpde, hper⟩

end OAI.Analysis.PDE.Weak
