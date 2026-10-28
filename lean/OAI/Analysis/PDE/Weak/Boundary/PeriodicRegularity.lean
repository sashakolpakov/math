import OAI.Analysis.PDE.Weak.Boundary.CurvedRegularity
import OAI.Analysis.PDE.Variational.BoundaryH1

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The actual periodic variational solution has a classical zero-boundary
representative in a neighborhood of every regular boundary point,
including points on fundamental-cell seams. -/
theorem periodic_weak_solution_boundary_representative
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i)
    (r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hr : ContDiff ℝ ∞ r)
    (hΩ : ∀ z x, r (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) < 0 → r x < 0)
    (k : Fin (m+1)) (hk : k ∉ J)
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      ¬ r (k.insertNth (b k) y) < 0)
    (u : OAI.Analysis.PDE.Variational.PeriodicH10 a b {x | r x < 0} (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b-a)))
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hfg : ∀ᵐ y ∂volume, r y < 0 → OAI.Analysis.PDE.Variational.periodicRepresentative J a b f y = g y)
    (hweak : WeakDivergenceEquation {x | r x < 0}
      (fun y => A y (OAI.Analysis.PDE.Variational.periodicRepresentative J a b u.val y)) (OAI.Analysis.PDE.Variational.periodicRepresentative J a b f))
    {V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hV : IsOpen V) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ y ∈ V, ∀ z, lam * ‖z‖^2 ≤ inner ℝ (A y z) z)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (htrans : closure {x | r x < 0} ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hcoeff : closure {x | r x < 0} ⊆ V)
    (q : ℕ) (hq : 2 ≤ q) :
    ∀ x ∈ closure {x | r x < 0} \ {x | r x < 0},
      ∃ (O : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
        IsOpen O ∧ x ∈ O ∧ ContDiff ℝ q v ∧
        (∀ᵐ y ∂volume, y ∈ {x | r x < 0} ∩ O →
          v y = OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.periodicValue a b {x | r x < 0} _ u) y) ∧
        (∀ y ∈ (closure {x | r x < 0} \ {x | r x < 0}) ∩ O, v y = 0) := by
  intro x hx
  have hzero (z : OAI.Analysis.PDE.Variational.CellCoordinates m) (hz : z ∈ closure {x | r x < 0} \ {x | r x < 0}) :
      r z = 0 := by
    have hle : r z ≤ 0 := closure_minimal (fun y hy => le_of_lt hy)
      (isClosed_le hr.continuous continuous_const) hz.1
    have hge : 0 ≤ r z := le_of_not_gt hz.2
    linarith
  obtain ⟨U, p, F, hU, hxU, hp, he, hpe⟩ :=
    OAI.Analysis.PDE.Variational.periodicRepresentative_boundary_H1_equation J a b hab hL {x | r x < 0} hΩ k hk hface
      u A f hweak x (htrans hx.1)
  have he' : WeakDivergenceEquation ((U ∩ V) ∩ {x | r x < 0}) (fun y => A y (p.2 y)) g := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on he (fun y hy => ⟨hy.2, hy.1.1⟩)
    · exact Eventually.of_forall (fun _ _ => rfl)
    · filter_upwards [hpe, hfg] with y hy hf
      intro hyU
      exact (hf hyU.2).symm.trans (hy hyU.1.1).2.2.symm
  obtain ⟨O, v, hO, hxO, hOU, hv, hve, hvzero⟩ :=
    curved_boundary_weak_solution_classical r hr A hA hlam (hU.inter hV)
      (fun y hy => hell y hy.2) p hp g hg he' q hq
      ⟨hxU, hcoeff hx.1⟩ (hzero x hx) (hreg x (hzero x hx))
  refine ⟨O, v, hO, hxO, hv, ?_, ?_⟩
  · filter_upwards [hve, hpe] with y hy hpv
    intro hyO
    exact (hy hyO).symm.trans (hpv (hOU hyO.2).1).1
  · intro y hy
    exact hvzero y hy.2 (hzero y hy.1)

end OAI.Analysis.PDE.Weak
