import OAI.Analysis.PDE.Weak.PeriodicDirichletSmooth
import OAI.Analysis.PDE.Weak.PeriodicDirichletWeakExistence
import OAI.Analysis.PDE.Weak.Boundary.PeriodicRegularity

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Actual global periodic classical Dirichlet solvability on a regular
periodic sublevel domain. The proof constructs the weak solution, proves its
interior and boundary regularity, and glues its jets to a globally smooth
periodic representative. No inverse or regularity hypothesis is assumed. -/
theorem exists_global_periodic_classical_dirichlet_solution
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i)
    (r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hr : ContDiff ℝ ∞ r)
    (hΩ : ∀ z x, r (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) < 0 → r x < 0)
    (k : Fin (m+1)) (hk : k ∉ J)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    (hAp : ∀ z x, A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = A x)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y, r y < 0 → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y)
    {V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hV : IsOpen V) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ V, ∀ z, lam*‖z‖^2 ≤ inner ℝ (A x z) z)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (htrans : closure {x | r x < 0} ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hcoeff : closure {x | r x < 0} ⊆ V)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ u : OAI.Analysis.PDE.Variational.PeriodicH10 a b {x | r x < 0} (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b-a)),
      ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ,
        min lam 1*‖u‖ ≤ (2*(b k-a k))*‖f‖ ∧
        ContDiff ℝ q v ∧
        (∀ (z : J → ℤ) x, v (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = v x) ∧
        (∀ᵐ y, r y < 0 → v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b
          (OAI.Analysis.PDE.Variational.periodicValue a b {x | r x < 0} _ u) y) ∧
        (∀ x ∈ closure {y | r y < 0} \ {y | r y < 0}, v x = 0) ∧
        (∀ x, r x < 0 → -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) := by
  have hopen : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have htrans' : {x | r x < 0} ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b := subset_closure.trans htrans
  have hell' : ∀ x ∈ {x | r x < 0}, ∀ z, lam*‖z‖^2 ≤ inner ℝ (A x z) z :=
    fun x hx ↦ hell x (hcoeff (subset_closure hx))
  have hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      k.insertNth (b k) y ∉ {x | r x < 0} := by
    intro y _ hy
    have hlt := (htrans' hy k hk).2
    simp at hlt
  obtain ⟨u,hu,hue⟩ := exists_periodic_weak_solution_of_domain_ellipticity J a b hab hL
    {x | r x < 0} hopen htrans' hΩ k hface A hA.continuous hlam hell' hAp f
  have hbd := periodic_weak_solution_boundary_representative J a b hab hL r hr hΩ k hk
    hface u A hA f g hg hfg hu hV hlam hell hreg htrans hcoeff q hq
  obtain ⟨v,hv,hvp,hve,hvz,hvpde⟩ := periodic_weak_solution_global_smooth_dirichlet
    J a b hab hL {x | r x < 0} hopen htrans' hΩ k hk hface u A hA hlam hell' f hu g hg hfg q
    (fun x hx ↦ by
      obtain ⟨O,w,hO,hxO,hw,hwe,hwz⟩ := hbd x hx
      exact ⟨O,hO,hxO,w,hw.contDiffOn,hwe,hwz⟩)
  exact ⟨u,v,hue,hv,hvp,hve,hvz,hvpde⟩

end OAI.Analysis.PDE.Weak
