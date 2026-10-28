import Mathlib.Algebra.Homology.Homotopy

/-! # Homotopy Change Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.HomotopyChangeFrame

noncomputable section

/-! Change the frame arrow of an incoming homotopy before composing
it with a local coefficient map. -/

open _root_.CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]
  {A B I : CochainComplex C ℕ}
  (a : A ⟶ I) (f f' : A ⟶ B) (b : B ⟶ I)
  (h : Homotopy a (f ≫ b)) (hf : f' = f)

def homotopy : Homotopy a (f' ≫ b) :=
  h.trans (Homotopy.ofEq (congrArg (fun g => g ≫ b) hf.symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.HomotopyChangeFrame
