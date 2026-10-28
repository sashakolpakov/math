import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.BaseCechRefinement

/-! # Affine Common Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover

noncomputable section

/-! The intersection family is an actual common affine refinement
of two covers that agree after intersection with a distinguished open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} {ι κ : Type u}
  (U : ι → X.Opens) (V : κ → X.Opens)

def opens (a : ι × κ) : X.Opens := U a.1 ⊓ V a.2

def left : FormalCoproduct.mk (ι × κ) (opens U V) ⟶ FormalCoproduct.mk ι U where
  f := Prod.fst
  φ _ := homOfLE inf_le_left

def right : FormalCoproduct.mk (ι × κ) (opens U V) ⟶ FormalCoproduct.mk κ V where
  f := Prod.snd
  φ _ := homOfLE inf_le_right

theorem affine [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j)) (a : ι × κ) :
    IsAffineOpen (opens U V a) := (hU a.1).inf (hV a.2)

theorem covers (W O : X.Opens)
    (hU : iSup (fun i => W ⊓ U i) = O) (hV : iSup (fun j => W ⊓ V j) = O) :
    iSup (fun a => W ⊓ opens U V a) = O := by
  apply le_antisymm
  · apply iSup_le
    intro a
    exact (inf_le_inf_left W inf_le_left).trans (hU ▸ le_iSup (fun i => W ⊓ U i) a.1)
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ hx)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hV.symm ▸ hx)
    exact Opens.mem_iSup.mpr ⟨(i,j), hi.1, hi.2, hj.2⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover
