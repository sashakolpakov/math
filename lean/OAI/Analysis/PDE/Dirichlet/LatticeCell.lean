import OAI.Analysis.PDE.Dirichlet.RawCellMoore
import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives
import OAI.Analysis.PDE.Variational.PeriodicLocalL2
import Mathlib.LinearAlgebra.Basis.Prod

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

/-- Coordinates adapted to a given lattice and transverse splitting. No
orthogonality of the lattice basis is required. -/
def latticeCellEquiv (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ) : OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] E :=
  (((b.prod c).reindex d.symm).equivFun.symm.toContinuousLinearEquiv).trans e.symm

def latticeCellIndices (d : Fin (m + 1) ≃ ι ⊕ κ) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun i ↦ (d i).isLeft)

omit [Fintype ι] [Fintype κ] in
@[simp] theorem inl_mem_latticeCellIndices (d : Fin (m + 1) ≃ ι ⊕ κ) (i : ι) :
    d.symm (Sum.inl i) ∈ latticeCellIndices d := by
  simp [latticeCellIndices]

omit [Fintype ι] [Fintype κ] in
@[simp] theorem inr_not_mem_latticeCellIndices (d : Fin (m + 1) ≃ ι ⊕ κ) (i : κ) :
    d.symm (Sum.inr i) ∉ latticeCellIndices d := by
  simp [latticeCellIndices]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Fintype ι] [Fintype κ] in
theorem latticeCellEquiv_symm_apply (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ) (x : E) (i : Fin (m + 1)) :
    (latticeCellEquiv e b c d).symm x i = (b.prod c).repr (e x) (d i) := by
  change ((b.prod c).reindex d.symm).equivFun (e x) i = _
  simp only [Basis.equivFun_apply, Basis.repr_reindex_apply, Equiv.symm_symm]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Fintype ι] [Fintype κ] in
theorem latticeCellEquiv_inl_repr (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (i : ι) :
    b.repr (e (latticeCellEquiv e b c d x)).1 i = x (d.symm (Sum.inl i)) := by
  have h := latticeCellEquiv_symm_apply e b c d (latticeCellEquiv e b c d x)
    (d.symm (Sum.inl i))
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Equiv.apply_symm_apply,
    Basis.prod_repr_inl] using h.symm

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Fintype ι] [Fintype κ] in
theorem latticeCellEquiv_inr_repr (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (i : κ) :
    c.repr (e (latticeCellEquiv e b c d x)).2 i = x (d.symm (Sum.inr i)) := by
  have h := latticeCellEquiv_symm_apply e b c d (latticeCellEquiv e b c d x)
    (d.symm (Sum.inr i))
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Equiv.apply_symm_apply,
    Basis.prod_repr_inr] using h.symm

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] in
/-- A raw coordinate period becomes a vector of the original physical
lattice, with exactly zero transverse component. -/
theorem latticeCellEquiv_period (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ)
    (L : OAI.Analysis.PDE.Variational.CellCoordinates m) (hL : ∀ i ∈ latticeCellIndices d, L i = 1)
    (z : latticeCellIndices d → ℤ) :
    ∃ l : Submodule.span ℤ (Set.range b),
      e (latticeCellEquiv e b c d (OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z)) =
        ((l : P), 0) := by
  classical
  let w : ι → ℤ := fun i ↦ z ⟨d.symm (Sum.inl i), inl_mem_latticeCellIndices d i⟩
  let l : P := ∑ i, w i • b i
  have hl : l ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨⟨l, hl⟩, Prod.ext ?_ ?_⟩
  · apply b.equivFun.injective
    funext i
    change b.repr _ i = b.repr l i
    rw [latticeCellEquiv_inl_repr]
    have he : l = b.equivFun.symm (fun i ↦ (w i : ℝ)) := by
      simp only [l, Basis.equivFun_symm_apply, Int.cast_smul_eq_zsmul]
    rw [he]
    change OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z (d.symm (Sum.inl i)) =
      b.equivFun (b.equivFun.symm (fun i ↦ (w i : ℝ))) i
    rw [LinearEquiv.apply_symm_apply]
    simp [OAI.Analysis.PDE.Variational.coordinatePeriodShift, hL _ (inl_mem_latticeCellIndices d i), w]
  · apply c.equivFun.injective
    funext i
    change c.repr _ i = c.repr 0 i
    rw [latticeCellEquiv_inr_repr]
    simp [OAI.Analysis.PDE.Variational.coordinatePeriodShift, inr_not_mem_latticeCellIndices]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] in
theorem LatticePeriodic.comp_latticeCellEquiv {W : Type*}
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {f : E → W}
    (hf : LatticePeriodic e b f) (c : Basis κ ℝ V)
    (d : Fin (m + 1) ≃ ι ⊕ κ) (L : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ latticeCellIndices d, L i = 1)
    (z : latticeCellIndices d → ℤ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    f (latticeCellEquiv e b c d (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z)) =
      f (latticeCellEquiv e b c d x) := by
  obtain ⟨l, hl⟩ := latticeCellEquiv_period e b c d L hL z
  have he : latticeCellEquiv e b c d
      (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z) =
      e.symm ((e (latticeCellEquiv e b c d x)).1 + (l : P),
        (e (latticeCellEquiv e b c d x)).2) := by
    apply e.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, map_add, map_add, hl]
    apply Prod.ext <;> simp
  rw [he]
  exact hf _ l

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] in
/-- Every physical lattice translation arises from an integer raw-cell
translation. This converse is needed to return a periodic solution. -/
theorem latticeCellEquiv_period_surjective (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ)
    (L : OAI.Analysis.PDE.Variational.CellCoordinates m) (hL : ∀ i ∈ latticeCellIndices d, L i = 1)
    (l : Submodule.span ℤ (Set.range b)) :
    ∃ z : latticeCellIndices d → ℤ,
      e (latticeCellEquiv e b c d (OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z)) =
        ((l : P), 0) := by
  classical
  have hw : ∀ i, ∃ z : ℤ, (z : ℝ) = b.repr (l : P) i := by
    intro i
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ (l : P)).mp l.property i
    exact ⟨z, hz⟩
  choose w hw using hw
  let z : latticeCellIndices d → ℤ := fun i ↦ Sum.elim w (fun _ ↦ 0) (d i)
  refine ⟨z, Prod.ext ?_ ?_⟩
  · apply b.equivFun.injective
    funext i
    change b.repr _ i = b.repr (l : P) i
    rw [latticeCellEquiv_inl_repr, ← hw i]
    simp [OAI.Analysis.PDE.Variational.coordinatePeriodShift, hL _ (inl_mem_latticeCellIndices d i), z]
  · apply c.equivFun.injective
    funext i
    change c.repr _ i = c.repr 0 i
    rw [latticeCellEquiv_inr_repr]
    simp [OAI.Analysis.PDE.Variational.coordinatePeriodShift, inr_not_mem_latticeCellIndices]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] in
theorem latticePeriodic_of_coordinate_periodic {W : Type*}
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (c : Basis κ ℝ V)
    (d : Fin (m + 1) ≃ ι ⊕ κ) (L : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ latticeCellIndices d, L i = 1) {v : OAI.Analysis.PDE.Variational.CellCoordinates m → W}
    (hv : ∀ z x, v (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z) = v x) :
    LatticePeriodic e b (v ∘ (latticeCellEquiv e b c d).symm) := by
  intro x l
  obtain ⟨z, hz⟩ := latticeCellEquiv_period_surjective e b c d L hL l
  have he : latticeCellEquiv e b c d
      ((latticeCellEquiv e b c d).symm x + OAI.Analysis.PDE.Variational.coordinatePeriodShift (latticeCellIndices d) L z) =
      e.symm ((e x).1 + (l : P), (e x).2) := by
    apply e.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, map_add,
      ContinuousLinearEquiv.apply_symm_apply, map_add, hz]
    apply Prod.ext <;> simp
  change v ((latticeCellEquiv e b c d).symm _) = v ((latticeCellEquiv e b c d).symm x)
  rw [← he, ContinuousLinearEquiv.symm_apply_apply]
  exact hv z _

end OAI.Analysis.PDE.Dirichlet
