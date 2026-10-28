import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift

/-! # Affine Cover -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCover.Construction.FiniteAffineCover

noncomputable section

/-! Finite nonempty affine covers with a common nonempty affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

structure Data (X : Scheme.{u}) where
  n : ℕ
  opens : Fin n → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  nonempty : ∀ i, Nonempty (opens i)
  covers : ∀ x : X, ∃ i, x ∈ opens i
  common : X.Opens
  common_affine : IsAffineOpen common
  common_nonempty : Nonempty common
  common_le : ∀ i, common ≤ opens i

theorem nonempty (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] : Nonempty (Data X) := by
  classical
  have ha (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hUa hxU using ha
  have hcover : Set.univ ⊆ ⋃ x : X, (U x : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) hcover
  let e := (Fintype.equivFin s).symm
  let V : Fin (Fintype.card s) → X.Opens := fun i => U (e i).1
  have hV (i) : Nonempty (V i) := ⟨⟨(e i).1, hxU (e i).1⟩⟩
  have hη : genericPoint X ∈ iInf V := by
    change genericPoint X ∈ ((iInf V : X.Opens) : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter]
    intro i
    have := hV i
    exact GenericLift.Construction.GenericLiftRestriction.generic_mem (V i)
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hη (iInf V).isOpen
  refine ⟨⟨Fintype.card s, V, (fun i => hUa (e i).1), hV, ?_, W, hW,
    ⟨⟨genericPoint X, hηW⟩⟩, (fun i => hWV.trans (iInf_le V i))⟩⟩
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
  refine ⟨e.symm ⟨i, his⟩, ?_⟩
  change x ∈ U (e (e.symm ⟨i, his⟩)).1
  rw [e.apply_symm_apply]
  exact hxi

def ofIntegral (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] : Data X :=
  (FiniteAffineCover.nonempty X).some

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCover.Construction.FiniteAffineCover
