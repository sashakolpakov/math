import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.BoundaryRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryIdentity
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup

/-! # Factor Boundary Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryRefinement.Construction

noncomputable section

/-! The boundary changes in unit-center and disjoint-factor blowups are concrete finite refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def mergeDisjointExceptionalLabels {β : Type} : Option (Option β) → Option β
  | none => none
  | some none => none
  | some (some i) => some i

theorem boundaryRefinementFiber_merge_none {β : Type} [Fintype β] [DecidableEq β] :
    BoundaryRefinement.Construction.boundaryRefinementFiber (@mergeDisjointExceptionalLabels β) none = {none, some none} := by
  classical
  ext j
  rw [BoundaryRefinement.Construction.mem_boundaryRefinementFiber]
  rcases j with _ | (_ | j) <;> simp [mergeDisjointExceptionalLabels]

theorem boundaryRefinementFiber_merge_some {β : Type} [Fintype β] (i : β) :
    BoundaryRefinement.Construction.boundaryRefinementFiber (@mergeDisjointExceptionalLabels β) (some i) = {some (some i)} := by
  classical
  ext j
  rw [BoundaryRefinement.Construction.mem_boundaryRefinementFiber]
  rcases j with _ | (_ | j) <;> simp [mergeDisjointExceptionalLabels]

theorem boundaryRefinementFiber_some_none {β : Type} [Fintype β] :
    BoundaryRefinement.Construction.boundaryRefinementFiber (@some β) none = ∅ := by
  classical
  ext j
  simp [BoundaryRefinement.Construction.boundaryRefinementFiber]

theorem boundaryRefinementFiber_some_some {β : Type} [Fintype β] (i : β) :
    BoundaryRefinement.Construction.boundaryRefinementFiber (@some β) (some i) = {i} := by
  classical
  ext j
  simp [BoundaryRefinement.Construction.boundaryRefinementFiber]

theorem unit_adjoin_boundary_refinement {X : Scheme} {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) :
    BoundaryRefinement.Construction.DisjointBoundaryRefinement some (fun j => match j with | none => ⊤ | some i => D i) D := by
  constructor
  · intro i
    cases i with
    | none => rw [boundaryRefinementFiber_some_none, Finset.prod_empty]; rfl
    | some i => rw [boundaryRefinementFiber_some_some, Finset.prod_singleton]
  · intro i j hne hr
    exact False.elim (hne (Option.some.inj hr))

theorem globalBlowup_top_boundary_refinement
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (hI : (⊤ : X.IdealSheafData) ≠ ⊥) {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    BoundaryRefinement.Construction.DisjointBoundaryRefinement some (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary ⊤ hI D)
      (fun i => (D i).comap (GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI)) := by
  have he : CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary ⊤ hI D =
      (fun j => match j with | none => ⊤ | some i => (D i).comap (GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI)) := by
    funext j
    cases j with
    | none => exact Scheme.IdealSheafData.comap_top _
    | some i => exact Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center (D i) hI 1
  rw [he]
  exact unit_adjoin_boundary_refinement _

theorem disjointFactorBlowup_boundary_refinement
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) :
    BoundaryRefinement.Construction.DisjointBoundaryRefinement mergeDisjointExceptionalLabels
      (fun j => (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) D j).comap
        (FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint).hom)
      (FactorBoundaryIdentity.Construction.disjointFactorBlowupBoundary K L hK hL D) := by
  classical
  constructor
  · intro i
    cases i with
    | none =>
        rw [boundaryRefinementFiber_merge_none, Finset.prod_pair (by simp)]
        exact (FactorBoundaryIdentity.Construction.disjointFactorBlowupBoundary_exceptional_product K L hK hL hdisjoint D).trans (mul_comm _ _)
    | some i =>
        rw [boundaryRefinementFiber_merge_some, Finset.prod_singleton]
        exact FactorBoundaryIdentity.Construction.disjointFactorBlowupBoundary_old_label K L hK hL hdisjoint D i
  · intro i j hne hr
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp_all [mergeDisjointExceptionalLabels]
    all_goals simpa only [sup_comm] using FactorBoundaryIdentity.Construction.disjointFactorBlowupBoundary_exceptionals_disjoint K L hK hL hdisjoint D

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryRefinement.Construction
