import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlotSemantics
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! The precise order emitted by the native vertex/check loops. Each row is
present even when shortening removes every one of its local ports. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def chronologicalRows (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List (List (Fin m × SparseCode.F3)) :=
  (List.finRange (2^r)).flatMap fun i =>
    (List.ofFn fun a => slots m shifts Q false (WalshExistence.cubeEquiv r i) a) ++
    (List.ofFn fun a => slots m shifts Q true (WalshExistence.cubeEquiv r i) a)

def serializedRows (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List (List (Fin m × SparseCode.F3)) :=
  (chronologicalRows m shifts Q).reverse

def rowStream (b m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List Bool :=
  Encoding.encodeList (rowPayload b m) (serializedRows m shifts Q)

theorem chronologicalRows_length (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    (chronologicalRows m shifts Q).length=2^r*(2*t) := by
  simp [chronologicalRows,List.length_flatMap,List.sum_replicate,Nat.mul_comm
    ]
  omega

theorem serializedRows_length (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    (serializedRows m shifts Q).length=2^r*(2*t) := by
  simpa [serializedRows] using chronologicalRows_length (m:=m) shifts Q

theorem mem_serializedRows_iff (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (ss : List (Fin m × SparseCode.F3)) :
    ss∈serializedRows m shifts Q ↔
      ∃ side v a, slots m shifts Q side v a=ss := by
  simp only [serializedRows,List.mem_reverse,chronologicalRows,List.mem_flatMap,
    List.mem_finRange,true_and,List.mem_append,List.mem_ofFn]
  constructor
  · rintro ⟨i,⟨a,h⟩|⟨a,h⟩⟩
    · exact ⟨false,WalshExistence.cubeEquiv r i,a,h⟩
    · exact ⟨true,WalshExistence.cubeEquiv r i,a,h⟩
  · rintro ⟨side,v,a,h⟩
    refine ⟨(WalshExistence.cubeEquiv r).symm v,?_⟩
    cases side
    · exact Or.inl ⟨a,by simpa using h⟩
    · exact Or.inr ⟨a,by simpa using h⟩

theorem serializedRows_slots_bound (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (ss : List (Fin m × SparseCode.F3)) (h : ss∈serializedRows m shifts Q) :
    ss.length ≤ D := by
  obtain ⟨side,v,a,rfl⟩ := (mem_serializedRows_iff shifts Q ss).mp h
  exact slots_length shifts Q side v a

theorem rowStream_length_le (b : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    (rowStream b m shifts Q).length ≤ 1+(2*(D*b)+2)*(2^r*(2*t)) := by
  have h := Encoding.length_encodeList_upper (rowPayload b m)
    (serializedRows m shifts Q) (D*b) (by
      intro ss hs
      rw [rowPayload_length]
      exact Nat.mul_le_mul_right b (serializedRows_slots_bound shifts Q ss hs))
  simpa only [rowStream,serializedRows_length] using h

theorem serializedRows_covers (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (hm : m ≤ 2^r*D)
    (row : (Cayley.Cube r × Fin t) ⊕ (Cayley.Cube r × Fin t)) :
    (fun c => (Cayley.graph shifts).matrix Q row
      (SparseCode.edgeEquiv r D (Fin.castLE hm c))) ∈
      (serializedRows m shifts Q).map coefficient := by
  have one (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
      (fun c => (Cayley.graph shifts).matrix Q (matrixRow side v a)
        (SparseCode.edgeEquiv r D (Fin.castLE hm c))) ∈
        (serializedRows m shifts Q).map coefficient := by
    apply List.mem_map.mpr
    refine ⟨slots m shifts Q side v a,
      (mem_serializedRows_iff shifts Q _).mpr ⟨side,v,a,rfl⟩,?_⟩
    funext c
    exact slots_matrix shifts Q side v a hm c
  cases row with
  | inl va => exact one false va.1 va.2
  | inr va => exact one true va.1 va.2

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
