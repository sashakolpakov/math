import OAI.Analysis.PDE.Weak.Elliptic.GlobalBoundaryGlue
import OAI.Analysis.PDE.Variational.PeriodicLocalL2

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem closure_transverse_bounds
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ closure Ω) :
    ∀ i, i ∉ J → a i ≤ x i ∧ x i ≤ b i := by
  intro i hi
  constructor
  · exact closure_minimal (fun y hy ↦ (htrans hy i hi).1.le)
      (isClosed_le continuous_const (continuous_apply i)) hx
  · exact closure_minimal (fun y hy ↦ (htrans hy i hi).2.le)
      (isClosed_le (continuous_apply i) continuous_const) hx

theorem coordinateWrap_mem_closed_cell
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ J, a i < b i) {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hx : ∀ i, i ∉ J → a i ≤ x i ∧ x i ≤ b i) :
    OAI.Analysis.PDE.Variational.coordinateWrap J a (b-a) x ∈ Icc a b := by
  have hbnd (i : Fin (m+1)) :
      a i ≤ OAI.Analysis.PDE.Variational.coordinateWrap J a (b-a) x i ∧ OAI.Analysis.PDE.Variational.coordinateWrap J a (b-a) x i ≤ b i := by
    by_cases hi : i ∈ J
    · have hpos : 0 < b i-a i := sub_pos.mpr (hL i hi)
      have hlo := (le_div_iff₀ hpos).mp (Int.floor_le ((x i-a i)/(b i-a i)))
      have hhi := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one ((x i-a i)/(b i-a i)))
      simp only [OAI.Analysis.PDE.Variational.coordinateWrap,ite_eq_left hi,Pi.sub_apply]
      constructor <;> nlinarith
    · simpa only [OAI.Analysis.PDE.Variational.coordinateWrap,ite_eq_right hi] using hx i hi
  exact ⟨fun i ↦ (hbnd i).1, fun i ↦ (hbnd i).2⟩

/-- The actual transverse-bounded periodic geometry has a compact set of
representatives, including every boundary point and every cell seam. -/
theorem closed_domain_has_cell_representatives
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ J, a i < b i) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b) :
    ∀ x ∈ closure Ω, ∃ z : J → ℤ, x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∈ Icc a b := by
  intro x hx
  refine ⟨fun i ↦ -⌊(x i-a i)/(b i-a i)⌋,?_⟩
  have hw := coordinateWrap_mem_closed_cell J a b hL (closure_transverse_bounds J a b htrans hx)
  rw [OAI.Analysis.PDE.Variational.coordinateWrap_eq_add_shift] at hw
  simpa only [Pi.sub_apply] using hw

end OAI.Analysis.PDE.Weak
