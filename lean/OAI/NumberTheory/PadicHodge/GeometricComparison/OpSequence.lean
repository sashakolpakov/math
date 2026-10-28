import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Iso

/-! # Op Sequence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpSequence.OpSequenceIso

noncomputable section

/-! Isomorphisms of inverse sequences require only the actual
successor transition squares. -/

open _root_.CategoryTheory Opposite

variable {C : Type*} [Category* C] (F G : ℕᵒᵖ ⥤ C)
  (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
  (h : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
    (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op)

def iso : F ≅ G := NatIso.ofComponents (fun n => e n.unop)
  (fun {_ _} a => (NatTrans.ofOpSequence (fun n => (e n).hom) h).naturality a)

theorem hom_app (n : ℕ) : (iso F G e h).hom.app (op n) = (e n).hom := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpSequence.OpSequenceIso
