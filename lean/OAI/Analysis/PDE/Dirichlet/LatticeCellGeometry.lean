import OAI.Analysis.PDE.Dirichlet.LatticeCell

open Set Module
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E P V ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype ι] [Fintype κ]

def latticeCellLower (d : Fin (m + 1) ≃ ι ⊕ κ) (R : ℝ) : OAI.Analysis.PDE.Variational.CellCoordinates m :=
  fun i ↦ if (d i).isLeft then 0 else -R

def latticeCellUpper (d : Fin (m + 1) ≃ ι ⊕ κ) (R : ℝ) : OAI.Analysis.PDE.Variational.CellCoordinates m :=
  fun i ↦ if (d i).isLeft then 1 else R

omit [Fintype ι] [Fintype κ] in
theorem latticeCellLower_le_upper (d : Fin (m + 1) ≃ ι ⊕ κ) {R : ℝ} (hR : 0 < R) :
    latticeCellLower d R ≤ latticeCellUpper d R := by
  intro i
  simp only [latticeCellLower, latticeCellUpper]
  split_ifs <;> linarith

omit [Fintype ι] [Fintype κ] in
theorem latticeCell_period_length (d : Fin (m + 1) ≃ ι ⊕ κ) (R : ℝ)
    (i : Fin (m + 1)) (hi : i ∈ latticeCellIndices d) :
    (latticeCellUpper d R - latticeCellLower d R) i = 1 := by
  have hid : (d i).isLeft := by simpa [latticeCellIndices] using hi
  simp [latticeCellUpper, latticeCellLower, hid]

omit [Fintype ι] [Fintype κ] in
theorem latticeCell_period_pos (d : Fin (m + 1) ≃ ι ⊕ κ) (R : ℝ)
    (i : Fin (m + 1)) (hi : i ∈ latticeCellIndices d) :
    latticeCellLower d R i < latticeCellUpper d R i := by
  have := latticeCell_period_length d R i hi
  change latticeCellUpper d R i - latticeCellLower d R i = 1 at this
  linarith

omit [FiniteDimensional ℝ P] [Fintype ι] in
/-- Compactness in the transverse factor supplies a strict cell margin.
The periodic coordinates keep unit periods, regardless of this radius. -/
theorem exists_latticeCell_transverse_bound (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ}
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C) :
    ∃ R : ℝ, 0 < R ∧
      {x | r (latticeCellEquiv e b c d x) ≤ 0} ⊆
        OAI.Analysis.PDE.Variational.transverseInterior (latticeCellIndices d) (latticeCellLower d R) (latticeCellUpper d R) := by
  obtain ⟨R, hR, hRC⟩ :=
    (hC.image c.equivFun.toContinuousLinearEquiv.continuous).isBounded.exists_pos_norm_lt
  refine ⟨R, hR, ?_⟩
  intro x hx i hi
  have hnot : ¬(d i).isLeft := by simpa [latticeCellIndices] using hi
  obtain ⟨j, hj⟩ : ∃ j : κ, d i = Sum.inr j := by
    cases hd : d i with
    | inl j => simp [hd] at hnot
    | inr j => exact ⟨j, rfl⟩
  have hi' : d.symm (Sum.inr j) = i := by rw [← hj, Equiv.symm_apply_apply]
  have hnorm : ‖c.equivFun (e (latticeCellEquiv e b c d x)).2‖ < R :=
    hRC _ ⟨_, hbounded _ hx, rfl⟩
  have hcoord : |x i| < R := by
    have h := (norm_le_pi_norm (c.equivFun (e (latticeCellEquiv e b c d x)).2) j).trans_lt hnorm
    change ‖c.repr (e (latticeCellEquiv e b c d x)).2 j‖ < R at h
    rwa [latticeCellEquiv_inr_repr, hi', Real.norm_eq_abs] at h
  simpa [latticeCellLower, latticeCellUpper, hj] using abs_lt.mp hcoord

end OAI.Analysis.PDE.Dirichlet
