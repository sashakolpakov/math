import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

namespace OAI.Algorithms

/-!
# The supplied ring model uses the polynomial actually found by search
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

/-- Execution coefficients with their proved irreducibility certificate. -/
def data {d : ℕ} (hd : 0 < d) : RingModel.Data d where
  coefficients := coefficients d
  irreducible := coefficients_irreducible hd

@[simp] theorem data_coefficients {d : ℕ} (hd : 0 < d) :
    (data hd).coefficients = coefficients d := rfl

theorem data_residuePolynomial {d : ℕ} (hd : 0 < d) :
    (data hd).residuePolynomial = QuarticSearch.poly (coefficients d) := rfl

theorem data_F {d : ℕ} (hd : 0 < d) (t : ℕ) :
    (data hd).F t = QuarticSearch.poly (liftedCoefficients d t) := rfl

/-- The actual nested coefficient array for multiplication in the lift ring. -/
def suppliedTable (d t : ℕ) :
    List.Vector (List.Vector (List.Vector (ZMod (3 ^ t)) d) d) d :=
  storedTable (liftedCoefficients d t)

theorem suppliedTable_correct {d : ℕ} (hd : 0 < d) (t : ℕ) (ht : 0 < t)
    (i j k : Fin d) :
    (((suppliedTable d t).get i).get j).get k =
      ((Polynomial.X ^ (i.val + j.val)) %ₘ (data hd).F t).coeff k.val := by
  let _ : Fact (1 < 3 ^ t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  exact storedTable_eq_coeff hd (liftedCoefficients d t) i j k

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
