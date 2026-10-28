import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-! # Scheme Chain Stalk Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeChainStalkDimension

noncomputable section

/-! A chain of irreducible closed subsets through a point embeds into
the spectrum of its actual local ring. Its length is therefore bounded
by the Krull dimension of that stalk. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Topology _root_.Order
universe u

theorem scheme_irreducibleChain_length_le_stalkDimension
    (X : Scheme.{u}) (C : LTSeries (IrreducibleCloseds X)) (x : X) (hx : x ∈ C.head) :
    (C.length : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  let f := X.fromSpecStalk x
  let a (i : Fin (C.length + 1)) := (C i).isIrreducible.genericPoint
  have ha (i : Fin (C.length + 1)) : IsGenericPoint (a i) (C i : Set X) :=
    (C i).isIrreducible.isGenericPoint_genericPoint (C i).isClosed
  have hlift (i : Fin (C.length + 1)) : ∃ y : Spec (X.presheaf.stalk x), f y = a i := by
    change a i ∈ Set.range (X.fromSpecStalk x)
    rw [Scheme.range_fromSpecStalk]
    exact (ha i).specializes (C.head_le i hx)
  choose y hy using hlift
  have hpre (i : Fin (C.length + 1)) :
      closure ({y i} : Set (Spec (X.presheaf.stalk x))) = f ⁻¹' (C i : Set X) := by
    rw [f.isEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hy i, (ha i).def]
  let qpoint (i : Fin (C.length + 1)) : IrreducibleCloseds (Spec (X.presheaf.stalk x)) :=
    ⟨closure {y i}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hstrict : StrictMono qpoint := by
    intro i j hij
    apply lt_of_le_not_ge
    · change closure ({y i} : Set (Spec (X.presheaf.stalk x))) ⊆ closure {y j}
      rw [hpre, hpre]
      exact Set.preimage_mono (C.monotone hij.le)
    · intro hji
      have hz : y j ∈ closure ({y i} : Set (Spec (X.presheaf.stalk x))) :=
        hji (subset_closure (Set.mem_singleton _))
      rw [hpre] at hz
      change f (y j) ∈ (C i : Set X) at hz
      rw [hy j] at hz
      exact (C.strictMono hij).not_ge ((ha j).mem_closed_set_iff (C i).isClosed |>.mp hz)
  let q : LTSeries (IrreducibleCloseds (Spec (X.presheaf.stalk x))) := LTSeries.mk C.length qpoint hstrict
  have h : (C.length : WithBot ℕ∞) ≤ topologicalKrullDim (Spec (X.presheaf.stalk x)) := q.length_le_krullDim
  exact h.trans_eq (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeChainStalkDimension
