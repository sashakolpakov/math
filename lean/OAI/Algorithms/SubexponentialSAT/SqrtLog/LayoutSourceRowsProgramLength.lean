import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem RowProperty.coefficient_count {B d : ℕ} (hB : 0 < B) (hd : 0 < d)
    (R : ℕ → List (DensePolynomialProgram.Coeff B d) → Prop)
    (D j : ℕ) (rows : List (List (DensePolynomialProgram.Coeff B d)))
    (h : RowProperty DensePolynomialProgram.encode R (D*(d*B)) j rows)
    (i : Fin rows.length) :
    R (j+i.val) (rows.get i) ∧ (rows.get i).length=D := by
  obtain ⟨hr,hlen⟩ := RowProperty.get _ _ _ _ _ h i
  rw [DensePolynomialProgram.encode_length] at hlen
  have hn : 0 < d*B := Nat.mul_pos hd hB
  exact ⟨hr,(Nat.mul_right_cancel_iff hn).mp hlen⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
