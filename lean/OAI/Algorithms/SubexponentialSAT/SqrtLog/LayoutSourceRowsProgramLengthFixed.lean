import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramLength
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixedBasic

namespace OAI.Algorithms

/-! Proof-only refinement of the actual output rows to fixed-length arrays.
The byte stream is unchanged, so this adds no executable conversion. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

private theorem fixed_encodeList {B d D : ℕ}
    (rows : List (DensePolynomialProgram.Fixed.Array B d D)) :
    Encoding.encodeList DensePolynomialProgram.Fixed.encode rows=
      Encoding.encodeList DensePolynomialProgram.encode (rows.map Subtype.val) := by
  induction rows with
  | nil => rfl
  | cons w ws ih => simp [Encoding.encodeList,DensePolynomialProgram.Fixed.encode,ih]

theorem RowProperty.toFixed {B d : ℕ} (hB : 0 < B) (hd : 0 < d)
    (R : ℕ → List (DensePolynomialProgram.Coeff B d) → Prop)
    (D j : ℕ) (rows : List (List (DensePolynomialProgram.Coeff B d)))
    (h : RowProperty DensePolynomialProgram.encode R (D*(d*B)) j rows) :
    ∃ fixed : List (DensePolynomialProgram.Fixed.Array B d D),
      fixed.map Subtype.val=rows ∧ fixed.length=rows.length ∧
      Encoding.encodeList DensePolynomialProgram.Fixed.encode fixed=
        Encoding.encodeList DensePolynomialProgram.encode rows ∧
      RowProperty DensePolynomialProgram.Fixed.encode (fun k a=>R k a.val) (D*(d*B)) j fixed := by
  have hp : ∃ fixed : List (DensePolynomialProgram.Fixed.Array B d D),
      fixed.map Subtype.val=rows ∧
      RowProperty DensePolynomialProgram.Fixed.encode (fun k a=>R k a.val) (D*(d*B)) j fixed := by
    induction rows generalizing j with
    | nil => exact ⟨[],rfl,True.intro⟩
    | cons w ws ih =>
      obtain ⟨hr,hlen,htail⟩ := h
      have hw : w.length=D := by
        rw [DensePolynomialProgram.encode_length] at hlen
        exact (Nat.mul_right_cancel_iff (Nat.mul_pos hd hB)).mp hlen
      obtain ⟨tail,he,hprop⟩ := ih (j+1) htail
      refine ⟨⟨w,hw⟩::tail,?_,hr,?_,hprop⟩
      · simp [he]
      · exact DensePolynomialProgram.Fixed.encode_length ⟨w,hw⟩
  obtain ⟨fixed,he,hprop⟩ := hp
  refine ⟨fixed,he,?_,?_,hprop⟩
  · simpa using congrArg List.length he
  · rw [fixed_encodeList,he]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
