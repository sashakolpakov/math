import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace OAI.Algorithms

/-! Coordinatewise meaning and serialization facts for the completed source
table. The row order is the original ambient order. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem RowProperty.getElem {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W j : ℕ) (ws : List Wit)
    (h : RowProperty encode R W j ws) (i : ℕ) (hi : i < ws.length) :
    R (j+i) ws[i] ∧ (encode ws[i]).length=W := by
  induction ws generalizing j i with
  | nil => simp at hi
  | cons w ws ih =>
      obtain ⟨hw,hlen,ht⟩ := h
      cases i with
      | zero => simpa using And.intro hw hlen
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1) ht i hi'

theorem RowProperty.get {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W j : ℕ) (ws : List Wit)
    (h : RowProperty encode R W j ws) (i : Fin ws.length) :
    R (j+i.val) (ws.get i) ∧ (encode (ws.get i)).length=W :=
  RowProperty.getElem encode R W j ws h i.val i.isLt

theorem encodeList_replicate {Wit : Type*} (encode : Wit → List Bool) (w : Wit) (N : ℕ) :
    Encoding.encodeList id (List.replicate N (encode w))=
      Encoding.encodeList encode (List.replicate N w) := by
  induction N with
  | zero => rfl
  | succ N ih => simp [List.replicate_succ,Encoding.encodeList,ih]

theorem RowProperty.replicate {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W : ℕ) (w : Wit)
    (hR : ∀ j, R j w) (hW : (encode w).length=W) (j N : ℕ) :
    RowProperty encode R W j (List.replicate N w) := by
  induction N generalizing j with
  | zero => trivial
  | succ N ih => exact ⟨hR j,hW,ih (j+1)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
