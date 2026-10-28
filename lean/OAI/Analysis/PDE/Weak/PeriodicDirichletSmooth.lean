import OAI.Analysis.PDE.Weak.Elliptic.GlobalBoundaryCell
import OAI.Analysis.PDE.Weak.Elliptic.Classical.Periodicity

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Global finite-order smooth representative of the genuine periodic weak
Dirichlet solution. Only the local boundary regularity is left as an explicit
input; all overlap, extension, periodicity, and classical equation conclusions
are proved here. -/
theorem periodic_weak_solution_global_smooth_dirichlet
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hΩ : ∀ z x, x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m+1)) (hk : k ∉ J)
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : OAI.Analysis.PDE.Variational.PeriodicH10 a b Ω (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b-a)))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ Ω, ∀ z, lam*‖z‖^2 ≤ inner ℝ (A x z) z)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : WeakDivergenceEquation Ω
      (fun y ↦ A y (OAI.Analysis.PDE.Variational.periodicRepresentative J a b u.val y)) (OAI.Analysis.PDE.Variational.periodicRepresentative J a b f))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y, y ∈ Ω → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y)
    (q : ℕ)
    (hbd : ∀ x ∈ closure Ω \ Ω, ∃ U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen U ∧ x ∈ U ∧
      ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ q v U ∧
        (∀ᵐ y, y ∈ Ω ∩ U → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) y) ∧
        (∀ y ∈ (closure Ω \ Ω) ∩ U, v y = 0)) :
    ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ q v ∧
      (∀ (z : J → ℤ) x, v (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = v x) ∧
      (∀ᵐ y, y ∈ Ω → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u) y) ∧
      (∀ x ∈ closure Ω \ Ω, v x = 0) ∧
      (∀ x ∈ Ω, -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) := by
  obtain ⟨v,hv,hve,hvpde,hvper⟩ := periodic_weak_solution_smooth_periodic
    J a b hab hL Ω hopen htrans hΩ k hk hface u A hA hlam hell f hweak g hg hfg
  obtain ⟨w,hw,hwp,hwe,hwz,hwae⟩ := global_periodic_dirichlet_representative
    (OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a))
    (OAI.Analysis.PDE.Variational.finite_coordinatePeriodShift_norm J (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi)))
    hopen (isCompact_Icc) hΩ (closed_domain_has_cell_representatives J a b hL htrans)
    q (OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b Ω _ u)) v
    (hv.of_le (by simp)) hve hvper hbd
  refine ⟨w,hw,fun z x ↦ hwp x z,hwae,hwz,?_⟩
  intro x hx
  have he : w =ᶠ[𝓝 x] v := Filter.Eventually.mono (hopen.mem_nhds hx) fun y hy ↦ hwe hy
  rw [classical_elliptic_operator_congr A he]
  exact hvpde x hx

end OAI.Analysis.PDE.Weak
