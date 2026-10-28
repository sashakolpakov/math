import OAI.NumberTheory.ArithmeticGroups.Lattices.FinSuccessorBasisLift
import OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalBasisLift
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBasisLift

/-! # Reduced Lattice Basis Existence -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedLatticeBasisExistence.Construction

noncomputable section

section

/-! Shortest-vector projection and bounded fractional lifting perform
one full step of triangular lattice-basis reduction. -/

open _root_.Module
open scoped Classical

theorem reduced_lattice_basis_successor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖) {n : ℕ}
    (d : FinSuccessorBasisLift.Construction.ReducedLatticeBasis (ProjectedLattice.Construction.projectedLattice Λ v.val) n) :
    Nonempty (FinSuccessorBasisLift.Construction.ReducedLatticeBasis Λ (n + 1)) := by
  obtain ⟨B, c, hB0, hBi⟩ := FractionalBasisLift.Construction.exists_fractional_basis_lift Λ v hv0 hmin d.latticeBasis
  obtain ⟨Q, hQ0, hQi, hQo⟩ := OrthogonalBasisLift.Construction.exists_orthogonal_basis_lift v.val hv0 d.orthogonalBasis d.orthogonal
  let B' := B.reindex (FinSuccessorBasisLift.Construction.unitSumFinSuccEquiv n)
  let Q' := Q.reindex (FinSuccessorBasisLift.Construction.unitSumFinSuccEquiv n)
  have hB'0 : B' 0 = v := (FinSuccessorBasisLift.Construction.basis_reindex_unitSumFinSucc_zero B).trans hB0
  have hB'i (i : Fin n) : (B' i.succ).val = (d.latticeBasis i).val.val + c i • v.val := by
    rw [show B' i.succ = B (Sum.inr i) from FinSuccessorBasisLift.Construction.basis_reindex_unitSumFinSucc_succ B i]
    exact (hBi i).2
  have hQ'0 : Q' 0 = v.val := (FinSuccessorBasisLift.Construction.basis_reindex_unitSumFinSucc_zero Q).trans hQ0
  have hQ'i (i : Fin n) : Q' i.succ = (d.orthogonalBasis i).val :=
    (FinSuccessorBasisLift.Construction.basis_reindex_unitSumFinSucc_succ Q i).trans (hQi i)
  have hrepr0 (x : E) : Q'.repr x 0 = Q.repr x (Sum.inl ()) := by
    dsimp only [Q']
    rw [Basis.repr_reindex_apply]
    rfl
  have hreprS (x : E) (i : Fin n) : Q'.repr x i.succ = Q.repr x (Sum.inr i) := by
    dsimp only [Q']
    rw [Basis.repr_reindex_apply]
    simp [FinSuccessorBasisLift.Construction.unitSumFinSuccEquiv]
  have hr00 : Q'.repr (B' 0).val 0 = 1 := by
    rw [hB'0, ← hQ'0]
    simp
  have hr0S (j : Fin n) : Q'.repr (B' 0).val j.succ = 0 := by
    rw [hB'0, ← hQ'0]
    simp
  have hrS0 (i : Fin n) : Q'.repr (B' i.succ).val 0 = c i := by
    rw [hB'i, hrepr0]
    exact OrthogonalBasisLift.Construction.orthogonal_lift_fractional_first v.val d.orthogonalBasis Q hQ0 hQi (d.latticeBasis i).val (c i)
  have hrSS (i j : Fin n) : Q'.repr (B' i.succ).val j.succ =
      d.orthogonalBasis.repr (d.latticeBasis i).val j := by
    rw [hB'i, hreprS]
    exact OrthogonalBasisLift.Construction.orthogonal_lift_fractional_rest v.val d.orthogonalBasis Q hQ0 hQi (d.latticeBasis i).val (c i) j
  refine ⟨{
    latticeBasis := B'
    orthogonalBasis := Q'
    orthogonal := ?_
    upper := ?_
    diagonal := ?_
    reduced := ?_
    gap := ?_ }⟩
  · intro i j hij
    simpa only [Q', Basis.reindex_apply] using
      hQo (fun h => hij ((FinSuccessorBasisLift.Construction.unitSumFinSuccEquiv n).symm.injective h))
  · intro i j hij
    revert j
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j _ => hr0S j) j
      intro h
      exact (lt_irrefl _ h).elim
    · intro j
      refine Fin.cases ?_ (fun j h => ?_) j
      · intro h
        exact (Fin.not_lt_zero _ h).elim
      · rw [hrSS]
        exact d.upper i j (Fin.succ_lt_succ_iff.mp h)
  · intro i
    exact Fin.cases hr00 (fun i => (hrSS i i).trans (d.diagonal i)) i
  · intro i j hji
    revert j
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j h
      exact (Fin.not_lt_zero _ h).elim
    · intro j
      refine Fin.cases ?_ (fun j h => ?_) j
      · intro _
        rw [hrS0]
        exact (hBi i).1
      · rw [hrSS]
        exact d.reduced i j (Fin.succ_lt_succ_iff.mp h)
  · intro i j hij
    revert j
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j h => ?_) j
      · intro h
        simp at h
      · have hj : j.val = 0 := by simpa using h.symm
        rw [hQ'0, hQ'i, ← d.first_eq j hj]
        exact ProjectedLattice.Construction.shortest_vector_projection_gap Λ v.property hmin (d.latticeBasis j).property
          (fun hzero => d.latticeBasis.ne_zero j (Subtype.ext hzero))
    · intro j
      refine Fin.cases ?_ (fun j h => ?_) j
      · intro h
        simp at h
      · rw [hQ'i, hQ'i]
        exact d.gap i j (by simpa using h)

end

/-! Every full discrete integral lattice has a basis in bounded
upper triangular position relative to an orthogonal real basis. -/

open _root_.Module

theorem exists_reduced_lattice_basis (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (hdim : finrank ℝ E = n)
    (hfull : Submodule.span ℝ (Λ : Set E) = ⊤) : Nonempty (FinSuccessorBasisLift.Construction.ReducedLatticeBasis Λ n) := by
  induction n generalizing E with
  | zero =>
    let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact ⟨{
      latticeBasis := Basis.empty Λ
      orthogonalBasis := Basis.empty E
      orthogonal := fun i => Fin.elim0 i
      upper := fun i => Fin.elim0 i
      diagonal := fun i => Fin.elim0 i
      reduced := fun i => Fin.elim0 i
      gap := fun i => Fin.elim0 i }⟩
  | succ n ih =>
    have hnz : ∃ y ∈ Λ, y ≠ 0 := by
      by_contra! hz
      have he : (⊤ : Submodule ℝ E) = ⊥ := hfull.symm.trans
        (Submodule.span_eq_bot.mpr (fun x hx => hz x hx))
      have hf := congrArg (fun P : Submodule ℝ E => finrank ℝ P) he
      simp only [finrank_top, finrank_bot] at hf
      omega
    obtain ⟨y, hy, hy0⟩ := hnz
    obtain ⟨v, hv, hv0, hmin⟩ := ShortestVector.Construction.exists_shortest_lattice_vector Λ y hy hy0
    let W : Submodule ℝ E := Submodule.span ℝ {v}
    let Λ' := ProjectedLattice.Construction.projectedLattice Λ v
    let : DiscreteTopology Λ' := ProjectedLattice.Construction.projected_lattice_discrete Λ hv hv0 hmin
    have hdim' : finrank ℝ Wᗮ = n := by
      have he := W.finrank_add_finrank_orthogonal
      have hw : finrank ℝ W = 1 := finrank_span_singleton hv0
      omega
    obtain ⟨d⟩ := ih Λ' hdim' (ProjectedLattice.Construction.projected_lattice_full Λ hfull v)
    exact reduced_lattice_basis_successor Λ ⟨v, hv⟩ hv0 hmin d

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedLatticeBasisExistence.Construction
