import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledComaximalProducts
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointCenterSequence

/-! # Boundary Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.BoundaryRefinement.Construction

noncomputable section

/-! Finite refinements split boundary labels into disjoint native factors and persist under canonical blowup transforms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def boundaryRefinementFiber {β γ : Type} [Fintype γ] (r : γ → β) (i : β) : Finset γ := by
  classical
  exact Finset.univ.filter (fun j => r j = i)

theorem mem_boundaryRefinementFiber {β γ : Type} [Fintype γ] (r : γ → β) (i : β) (j : γ) :
    j ∈ boundaryRefinementFiber r i ↔ r j = i := by
  classical
  simp [boundaryRefinementFiber]

theorem boundaryRefinementFiber_option_none {β γ : Type} [Fintype γ] (r : γ → β) :
    boundaryRefinementFiber (Option.map r) none = {none} := by
  classical
  ext j
  cases j <;> simp [boundaryRefinementFiber]

theorem boundaryRefinementFiber_option_some {β γ : Type} [Fintype γ] (r : γ → β) (i : β) :
    boundaryRefinementFiber (Option.map r) (some i) =
      (boundaryRefinementFiber r i).map Function.Embedding.some := by
  classical
  ext j
  cases j <;> simp [boundaryRefinementFiber]

structure DisjointBoundaryRefinement {X : Scheme} {β γ : Type} [Fintype γ]
    (r : γ → β) (D : β → X.IdealSheafData) (E : γ → X.IdealSheafData) : Prop where
  product : ∀ i, D i = ∏ j ∈ boundaryRefinementFiber r i, E j
  disjoint : ∀ i j, i ≠ j → r i = r j → E i ⊔ E j = ⊤

theorem DisjointBoundaryRefinement.comap
    {X Y : Scheme} {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (B : DisjointBoundaryRefinement r D E) (q : Y ⟶ X) :
    DisjointBoundaryRefinement r (fun i => (D i).comap q) (fun j => (E j).comap q) := by
  constructor
  · intro i
    rw [B.product i, Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod]
  · intro i j hij hr
    rw [← Scheme.IdealSheafData.comap_sup, B.disjoint i j hij hr, Scheme.IdealSheafData.comap_top]

theorem DisjointBoundaryRefinement.blowup
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {β γ : Type} [Fintype γ] {r : γ → β}
    {D : β → X.IdealSheafData} {E : γ → X.IdealSheafData}
    (B : DisjointBoundaryRefinement r D E) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    DisjointBoundaryRefinement (Option.map r) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI E) := by
  constructor
  · intro i
    cases i with
    | none => rw [boundaryRefinementFiber_option_none, Finset.prod_singleton]; rfl
    | some i =>
        rw [boundaryRefinementFiber_option_some, Finset.prod_map]
        change GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (D i) hI 1 =
          ∏ j ∈ boundaryRefinementFiber r i, GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (E j) hI 1
        rw [B.product i]
        apply ControlledComaximalProducts.Construction.globalBlowupControlledIdeal_finset_comaximal_product
        intro j hj k hk hne
        exact B.disjoint j k hne
          ((mem_boundaryRefinementFiber r i j).mp hj |>.trans ((mem_boundaryRefinementFiber r i k).mp hk).symm)
  · intro i j hij hr
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some j => cases hr
    | some i =>
        cases j with
        | none => cases hr
        | some j =>
            exact ControlledComaximalProducts.Construction.globalBlowupControlledIdeal_preserves_sup_top I (E i) (E j) hI 1
              (B.disjoint i j (fun h => hij (congrArg some h)) (Option.some.inj hr))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.BoundaryRefinement.Construction
