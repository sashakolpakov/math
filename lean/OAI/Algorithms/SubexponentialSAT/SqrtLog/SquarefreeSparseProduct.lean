import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparse

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

structure Index (V : Type*) where
  u : ℕ
  z : ℕ
  vars : Finset V
  deriving DecidableEq

namespace Index

variable {V : Type*} [DecidableEq V]

def join (a b : Index V) : Index V := ⟨a.u + b.u, a.z + b.z, a.vars ∪ b.vars⟩
def Kept (t J : ℕ) (a : Index V) : Prop := a.u < t ∧ a.z < J
instance (t J : ℕ) (a : Index V) : Decidable (a.Kept t J) := inferInstanceAs (Decidable (_ ∧ _))

def Valid (a : Index V) : Prop := a.vars.card ≤ a.z

theorem Valid.join {a b : Index V} (ha : a.Valid) (hb : b.Valid) : (a.join b).Valid :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

end Index

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

noncomputable def atom (a : Index V) (c : R) : Jet V R :=
  Polynomial.monomial a.u (Polynomial.monomial a.z (monomial a.vars c))

@[simp] theorem atom_zero (a : Index V) : atom a (0 : R) = 0 := by
  simp [atom, monomial]

theorem atom_add (a : Index V) (c d : R) : atom a (c + d) = atom a c + atom a d := by
  simp [atom, monomial ]

theorem atom_mul (a b : Index V) (c d : R) : atom a c * atom b d = atom (a.join b) (c*d) := by
  simp [atom, Index.join, Polynomial.monomial_mul_monomial, monomial_mul]

theorem atom_admissible (a : Index V) (c : R) (ha : a.Valid) : Admissible (atom a c) :=
  admissible_monomial _ _ (zAdmissible_monomial _ _ (bounded_monomial _ _ ha))

theorem canonical_atom (t J : ℕ) (a : Index V) (c : R) :
    canonical t J (atom a c) = if a.Kept t J then atom a c else 0 := by
  by_cases ht : a.u < t <;> by_cases hj : a.z < J
  all_goals simp only [Index.Kept, ht, hj, and_self, and_false, false_and, ite_true, ite_false]
  all_goals ext u z
  all_goals by_cases hu : u = a.u <;> by_cases hz : z = a.z <;>
    subst_vars <;> simp_all [atom, coeff_canonical, Polynomial.coeff_monomial, eq_comm]
  all_goals split_ifs <;> first | rfl | omega

def row (t J : ℕ) (a : Index V × R) : Data (Index V) R → Data (Index V) R
  | [] => []
  | b :: l =>
      if (a.1.join b.1).Kept t J then (a.1.join b.1, a.2*b.2) :: row t J a l
      else row t J a l

def rawMul (t J : ℕ) : Data (Index V) R → Data (Index V) R → Data (Index V) R
  | [], _ => []
  | a :: l, b => row t J a b ++ rawMul t J l b

def mul (t J : ℕ) (a b : Data (Index V) R) : Data (Index V) R := normalize (rawMul t J a b)

noncomputable abbrev denote (l : Data (Index V) R) : Jet V R := decode atom l

theorem denote_row (t J : ℕ) (a : Index V × R) (b : Data (Index V) R) :
    denote (row t J a b) = canonical t J (atom a.1 a.2 * denote b) := by
  induction b with
  | nil => simp [row, denote, decode]
  | cons h b ih =>
      simp only [row, denote, decode, mul_add, map_add, atom_mul]
      rw [canonical_atom]
      by_cases hk : (a.1.join h.1).Kept t J <;> simp [hk, decode, ih, denote]

theorem denote_rawMul (t J : ℕ) (a b : Data (Index V) R) :
    denote (rawMul t J a b) = canonical t J (denote a * denote b) := by
  induction a with
  | nil => simp [rawMul, denote, decode]
  | cons h a ih =>
      rw [rawMul, denote, decode_append]
      change denote (row t J h b) + denote (rawMul t J a b) = _
      rw [denote_row, ih]
      simp only [denote, decode, add_mul, map_add]

theorem denote_mul (t J : ℕ) (a b : Data (Index V) R) :
    denote (mul t J a b) = canonical t J (denote a * denote b) := by
  rw [mul, denote, decode_normalize atom atom_zero atom_add]
  exact denote_rawMul t J a b

theorem mul_nodup (t J : ℕ) (a b : Data (Index V) R) :
    (keys (mul t J a b)).Nodup := nodup_normalize _

theorem row_length_le (t J : ℕ) (a : Index V × R) (b : Data (Index V) R) :
    (row t J a b).length ≤ b.length := by
  induction b with
  | nil => simp [row]
  | cons h b ih =>
      by_cases hk : (a.1.join h.1).Kept t J <;> simp [row, hk] <;> omega

theorem rawMul_length_le (t J : ℕ) (a b : Data (Index V) R) :
    (rawMul t J a b).length ≤ a.length * b.length := by
  induction a with
  | nil => simp [rawMul]
  | cons h a ih =>
      have hl := row_length_le t J h b
      simp only [rawMul, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
