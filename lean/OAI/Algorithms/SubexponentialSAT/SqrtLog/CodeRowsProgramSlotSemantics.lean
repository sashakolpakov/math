import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlots

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def coefficient (ss : List (Fin m × SparseCode.F3)) (c : Fin m) : SparseCode.F3 :=
  (ss.map fun s => if s.1=c then s.2 else 0).sum

theorem coefficient_filterMap (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (ps : List (Fin D)) (c : Fin m) :
    coefficient (ps.filterMap (slot m shifts Q side v a)) c =
      (ps.map fun p => if (index shifts side v p).val=c.val then Q a p else 0).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hm : (index shifts side v p).val < m
    · have he : (⟨(index shifts side v p).val,hm⟩ : Fin m)=c ↔
          (index shifts side v p).val=c.val := Fin.ext_iff
      simpa [coefficient,slot,hm,he] using congrArg
        (fun z => (if (index shifts side v p).val=c.val then Q a p else 0)+z) ih
    · have hn : (index shifts side v p).val≠c.val := by intro h; have := c.isLt; omega
      simpa [coefficient,slot,hm,hn] using ih

theorem coefficient_slots (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (c : Fin m) :
    coefficient (slots m shifts Q side v a) c =
      ∑ p : Fin D, if (index shifts side v p).val=c.val then Q a p else 0 := by
  rw [slots,coefficient_filterMap]
  simpa using (List.sum_toFinset
    (fun p : Fin D => if (index shifts side v p).val=c.val then Q a p else 0)
    (List.nodup_finRange D)).symm

def matrixRow (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    (Cayley.Cube r × Fin t) ⊕ (Cayley.Cube r × Fin t) :=
  if side then Sum.inr (v,a) else Sum.inl (v,a)

theorem edge_eq_iff (shifts : Fin D → Cayley.Cube r) (side : Bool)
    (v : Cayley.Cube r) (p : Fin D) (e : Cayley.Cube r × Fin D) :
    edge shifts side v p=e ↔ p=e.2 ∧ (if side then e.1+shifts e.2 else e.1)=v := by
  rcases e with ⟨w,q⟩
  cases side
  · simp [edge,Prod.mk.injEq,and_comm,eq_comm]
  · constructor
    · intro h
      have hp : p=q := congrArg Prod.snd h
      subst p
      have hv : v+shifts q=w := congrArg Prod.fst h
      refine ⟨rfl,?_⟩
      rw [←hv]
      simp [add_assoc]
    · rintro ⟨rfl,hv⟩
      apply Prod.ext
      · change v+shifts p=w
        rw [←hv]
        simp [add_assoc]
      · rfl

theorem edge_sum_matrix (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (e : Cayley.Cube r × Fin D) :
    (∑ p : Fin D, if edge shifts side v p=e then Q a p else 0) =
      (Cayley.graph shifts).matrix Q (matrixRow side v a) e := by
  simp_rw [edge_eq_iff]
  rcases e with ⟨w,q⟩
  cases side
  · by_cases h : w=v <;> simp [matrixRow,SparseCode.PortGraph.matrix,h]
  · by_cases h : w+shifts q=v <;> simp [matrixRow,SparseCode.PortGraph.matrix,Cayley.graph,h]

theorem slots_matrix (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (hm : m ≤ 2^r*D) (c : Fin m) :
    coefficient (slots m shifts Q side v a) c =
      (Cayley.graph shifts).matrix Q (matrixRow side v a)
        (SparseCode.edgeEquiv r D (Fin.castLE hm c)) := by
  rw [coefficient_slots]
  have hh (p : Fin D) : (index shifts side v p).val=c.val ↔
      edge shifts side v p=SparseCode.edgeEquiv r D (Fin.castLE hm c) := by
    constructor
    · intro h
      have he : index shifts side v p=Fin.castLE hm c := Fin.ext h
      have hv := congrArg (SparseCode.edgeEquiv r D) he
      simpa [index] using hv
    · intro h
      have hv := congrArg (SparseCode.edgeEquiv r D).symm h
      exact congrArg Fin.val (by simpa [index] using hv)
  simp_rw [hh]
  exact edge_sum_matrix shifts Q side v a _

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
