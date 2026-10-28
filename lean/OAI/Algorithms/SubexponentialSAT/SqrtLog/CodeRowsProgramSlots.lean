import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeConstruct
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def edge (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) : Cayley.Cube r × Fin D :=
  (if side then v+shifts p else v,p)

def index (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) : Fin (2^r*D) := (SparseCode.edgeEquiv r D).symm (edge shifts side v p)

theorem index_value (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r)
    (p : Fin D) :
    (index shifts side v p).val =
      ((WalshExistence.cubeEquiv r).symm (if side then v+shifts p else v)).val*D+p.val := by
  simp [index,SparseCode.edgeEquiv,edge,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

theorem index_injective (shifts : Fin D → Cayley.Cube r) (side : Bool) (v : Cayley.Cube r) :
    Function.Injective (index shifts side v) := by
  intro p q hpq
  have he := (SparseCode.edgeEquiv r D).symm.injective hpq
  exact congrArg Prod.snd he

def slot (m : ℕ) (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) (p : Fin D) :
    Option (Fin m × SparseCode.F3) :=
  if h : (index shifts side v p).val < m then some (⟨(index shifts side v p).val,h⟩,Q a p)
  else none

def slots (m : ℕ) (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) : List (Fin m × SparseCode.F3) :=
  (List.finRange D).filterMap (slot m shifts Q side v a)

theorem slots_length (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (slots m shifts Q side v a).length ≤ D := by
  exact (List.length_filterMap_le _ _).trans_eq List.length_finRange

theorem mem_slots_iff (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (side : Bool) (v : Cayley.Cube r) (a : Fin t) (s : Fin m × SparseCode.F3) :
    s ∈ slots m shifts Q side v a ↔
      ∃ p : Fin D, (index shifts side v p).val=s.1.val ∧ Q a p=s.2 := by
  simp only [slots,List.mem_filterMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨p,hp⟩
    unfold slot at hp
    split_ifs at hp with h
    · cases hp
      exact ⟨p,rfl,rfl⟩
  · rintro ⟨p,hi,hc⟩
    refine ⟨p,?_⟩
    have hm : (index shifts side v p).val < m := by rw [hi]; exact s.1.isLt
    simp only [slot,dite_eq_left hm,Option.some.injEq]
    exact Prod.ext (Fin.ext hi) hc

/-- Forward payload inside an outer row frame. The standard frame reader
returns its reversal, exactly the raw tuple ABI expected by the materializer. -/
def rowPayload (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) : List Bool :=
  (ss.map fun s => SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)).flatten

theorem rowPayload_length (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) :
    (rowPayload b m ss).length=ss.length*b := by
  induction ss with
  | nil => simp [rowPayload]
  | cons s ss ih =>
    change ((SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)) ++ rowPayload b m ss).length = _
    simp only [List.length_append,SubexpLiftRing.fixedBits_length,ih,List.length_cons]
    simp [Nat.add_mul,Nat.add_comm]

theorem sparse_rowPayload_length (b : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (rowPayload b m (slots m shifts Q side v a)).length ≤ D*b := by
  rw [rowPayload_length]
  exact Nat.mul_le_mul_right b (slots_length shifts Q side v a)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
