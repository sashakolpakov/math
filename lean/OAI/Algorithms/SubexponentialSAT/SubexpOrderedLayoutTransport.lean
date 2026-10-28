import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.OrderedScopeSystem
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero

namespace OAI.Algorithms

/-!
# Recovering the original factor indices from the physical layout

The physical producer indexes factors by their positions in its emitted
scope list. Pulling its layout back along that exact enumeration preserves
the nodes, supports and subspaces. The two selected CRT values agree because
both reconstruct the same finite factor count.
-/

namespace SubexponentialSAT.SubexpOrderedLayoutTransport

open SubexpLayoutSpec Subexp.OrderedScopeSystem Subexp.ConstructivePacking

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E : Type*} [Fintype F] [DecidableEq F] [Field E] [Algebra (ZMod p) E]
  (S : Factor.System (Fin D) F (ZMod p))
  (factors : FiniteEnumeration F) (scopeLists : F → List (Fin D))
  (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ S.scope e)

def scopeBack (e : F) (v : {v // v ∈ S.scope e}) :
    {v // v ∈ (system S factors scopeLists scopeMem).scope
      ((factorEquiv factors scopeLists).symm e)} :=
  ⟨v.val, (scope_iff S factors scopeLists scopeMem _ v.val).mpr
    (by simpa only [Equiv.apply_symm_apply] using v.property)⟩

/-- This is a reindexing of the actual produced layout, with the original
factor tables. No new assignment, packing, node order, or basis is chosen. -/
def pullback {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := E) (system S factors scopeLists scopeMem).toPattern c) :
    Layout (E := E) S.toPattern c where
  bounded := hP
  size_ge := L.size_ge
  extension_degree := L.extension_degree
  nodes := L.nodes
  support := L.support
  support_disjoint := L.support_disjoint
  support_upper := L.support_upper
  K := L.K
  supported := L.supported
  dimension_lower := L.dimension_lower
  color e := L.color ((factorEquiv factors scopeLists).symm e)
  row e v := L.row ((factorEquiv factors scopeLists).symm e)
    (scopeBack S factors scopeLists scopeMem e v)
  row_zero e v w := L.row_zero _ (scopeBack S factors scopeLists scopeMem e v) w
  row_degree e v w := L.row_degree _ (scopeBack S factors scopeLists scopeMem e v) w
  annihilation t e v g x hg hx :=
    L.annihilation t _ (scopeBack S factors scopeLists scopeMem e v) g x hg hx

theorem pullback_nodes {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := E) (system S factors scopeLists scopeMem).toPattern c) :
    (pullback S factors scopeLists scopeMem hP L).nodes = L.nodes := rfl

theorem pullback_support {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := E) (system S factors scopeLists scopeMem).toPattern c) :
    (pullback S factors scopeLists scopeMem hP L).support = L.support := rfl

theorem pullback_subspaces {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := E) (system S factors scopeLists scopeMem).toPattern c) :
    (pullback S factors scopeLists scopeMem hP L).K = L.K := rfl

theorem selectedNode_pullback {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := SubexpActualRing.E p)
      (system S factors scopeLists scopeMem).toPattern c) (i : Fin c.Q) :
    SubexpCRTAtZero.selectedNode S (pullback S factors scopeLists scopeMem hP L) i =
      SubexpCRTAtZero.selectedNode (system S factors scopeLists scopeMem) L i := rfl

/-- Both sides are the actual selected-ring reconstruction. Their equality
uses the proved factor-count invariance under the physical enumeration. -/
theorem selectedValue_pullback {c : Parameters p k Δ r tau} (hP : S.toPattern.Bounded k Δ)
    (L : Layout (E := SubexpActualRing.E p)
      (system S factors scopeLists scopeMem).toPattern c) (hD : 0 < D) :
    SubexpCRTAtZero.selectedValue (system S factors scopeLists scopeMem) L =
      SubexpCRTAtZero.selectedValue S (pullback S factors scopeLists scopeMem hP L) := by
  have hcard : 0 < Fintype.card (Fin D) := by simpa using hD
  rw [SubexpCRTAtZero.selectedValue_eq_count _ _ hcard,
    SubexpCRTAtZero.selectedValue_eq_count _ _ hcard,
    count_system S factors scopeLists scopeMem]

end SubexponentialSAT.SubexpOrderedLayoutTransport

end OAI.Algorithms
