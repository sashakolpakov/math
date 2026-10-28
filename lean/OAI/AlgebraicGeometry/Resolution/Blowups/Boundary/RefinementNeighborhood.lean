import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.BoundaryRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels

/-! # Refinement Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A disjoint boundary refinement becomes a partial relabelling with unit factors on actual neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood {X : Scheme} {γ : Type} [Fintype γ]
    (E : γ → X.IdealSheafData) (x : X) : X.Opens := by
  classical
  exact ⨅ j, if x ∈ (E j).support then ⊤ else (E j).support.compl

theorem Boundary.RefinementNeighborhood.Construction.mem_boundaryRefinementNeighborhood {X : Scheme} {γ : Type} [Fintype γ]
    (E : γ → X.IdealSheafData) (x : X) : x ∈ Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x := by
  classical
  change x ∈ ((⨅ j, if x ∈ (E j).support then ⊤ else (E j).support.compl : X.Opens) : Set X)
  rw [TopologicalSpace.Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro j
  split_ifs with h
  · trivial
  · exact h

theorem Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood_unit
    {X : Scheme} {γ : Type} [Fintype γ] (E : γ → X.IdealSheafData) (x : X)
    (j : γ) (hj : x ∉ (E j).support) :
    (E j).comap (Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x).ι = ⊤ := by
  classical
  have hle : Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x ≤ (E j).support.compl :=
    (iInf_le (fun k => if x ∈ (E k).support then ⊤ else (E k).support.compl) j).trans
      (by rw [ite_eq_right hj])
  exact ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support (E j) _ (fun y => hle y.property)

def Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel {X : Scheme} {β γ : Type}
    (r : γ → β) (E : γ → X.IdealSheafData) (x : X) (j : γ) : Option β := by
  classical
  exact if x ∈ (E j).support then some (r j) else none

theorem Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel_eq_some {X : Scheme} {β γ : Type}
    (r : γ → β) (E : γ → X.IdealSheafData) (x : X) (j : γ) (i : β) :
    Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel r E x j = some i ↔ x ∈ (E j).support ∧ r j = i := by
  classical
  by_cases hj : x ∈ (E j).support <;> simp [Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel, hj]

theorem Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement.eq_of_mem_support
    {X : Scheme} {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) (x : X) (i j : γ) (hr : r i = r j)
    (hi : x ∈ (E i).support) (hj : x ∈ (E j).support) : i = j := by
  by_contra hne
  have h : x ∈ (E i ⊔ E j).support := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hi, hj⟩
  rw [B.disjoint i j hne hr, Scheme.IdealSheafData.support_top] at h
  exact h

theorem Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement.partialLabel_injective
    {X : Scheme} {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) (x : X) (i j : γ) (s : β)
    (hi : Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel r E x i = some s)
    (hj : Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel r E x j = some s) : i = j := by
  have hi' := (Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel_eq_some r E x i s).mp hi
  have hj' := (Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel_eq_some r E x j s).mp hj
  exact B.eq_of_mem_support x i j (hi'.2.trans hj'.2.symm) hi'.1 hj'.1

theorem Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement.local_label_eq
    {X : Scheme} {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (B : Disjoint.BoundaryRefinement.Construction.DisjointBoundaryRefinement r D E) (x : X) (j : γ) :
    (E j).comap (Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x).ι =
      match Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel r E x j with
      | none => ⊤
      | some i => (D i).comap (Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E x).ι := by
  classical
  by_cases hj : x ∈ (E j).support
  · simp only [Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel, ite_eq_left hj]
    rw [B.product (r j), Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod]
    symm
    apply Finset.prod_eq_single j
    · intro k hk hkj
      have hnot : x ∉ (E k).support := fun h => hkj
        (B.eq_of_mem_support x k j ((Disjoint.BoundaryRefinement.Construction.mem_boundaryRefinementFiber r (r j) k).mp hk) h hj)
      exact (Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood_unit E x k hnot).trans
        Scheme.IdealSheafData.one_eq_top.symm
    · intro hnot
      exact False.elim (hnot ((Disjoint.BoundaryRefinement.Construction.mem_boundaryRefinementFiber r (r j) j).mpr rfl))
  · simp only [Boundary.RefinementNeighborhood.Construction.boundaryRefinementPartialLabel, ite_eq_right hj]
    exact Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood_unit E x j hj

end

end OAI.AlgebraicGeometry.Resolution.Blowups
