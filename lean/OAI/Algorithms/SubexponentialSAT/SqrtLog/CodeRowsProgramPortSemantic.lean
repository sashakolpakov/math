import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPort
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPrefix

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BinaryArithmetic

def vertexPairs {r : ℕ} (v s : Cayley.Cube r) : List (Bool × Bool) :=
  List.ofFn fun i => (decide (v i=1),decide (s i=1))

@[simp] theorem vertexPairs_first {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).map Prod.fst=vertexBits v := by
  simp [vertexPairs,vertexBits,List.map_ofFn,Function.comp_def]

@[simp] theorem vertexPairs_second {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).map Prod.snd=vertexBits s := by
  simp [vertexPairs,vertexBits,List.map_ofFn,Function.comp_def]

@[simp] theorem vertexPairs_length {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).length=r := List.length_ofFn

theorem portIndex_vertex {r D : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (side : Bool) (v : Cayley.Cube r) (p : Fin D)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hp : BinaryArithmetic.toNat (d.stacks 14)=p.val) :
    portIndex d (vertexPairs v (shifts p))=(index shifts side v p).val := by
  rw [portIndex,hside,vertexPairs,shifted_vertexBits,vertexBits_value,hD,hp,index_value]

theorem coefficientValue_ternary (c : SparseCode.F3) (m : ℕ) :
    coefficientValue (decide (c=1)) (decide (c=2)) m=m*c.val := by
  fin_cases c
  · change coefficientValue false false m=m*0
    simp [coefficientValue]
  · change coefficientValue true false m=m*1
    simp [coefficientValue]
  · change coefficientValue false true m=m*2
    simp [coefficientValue]
    omega

theorem portAccum_vertex {r D t m : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (p : Fin D) (b : ℕ)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hm : BinaryArithmetic.toNat (d.stacks 4)=m) (hp : BinaryArithmetic.toNat (d.stacks 14)=p.val)
    (hb : (d.stacks 5).length=b) :
    portAccum d (decide (Q a p=1)) (decide (Q a p=2)) (vertexPairs v (shifts p))=
      (rowPayload b m (slot m shifts Q side v a p).toList).reverse++d.stacks 13 := by
  rw [portAccum,portIndex_vertex d shifts side v p hside hD hp,hm,hb,coefficientValue_ternary]
  by_cases h : (index shifts side v p).val  <  m <;>
    simp [h,slot,rowPayload]

theorem portAccum_prefix {r D t m : ℕ} (d : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i b : ℕ) (hi : i < D) (tail : List Bool)
    (hside : d.regs 12=side) (hD : BinaryArithmetic.toNat (d.stacks 3)=D)
    (hm : BinaryArithmetic.toNat (d.stacks 4)=m) (hp : BinaryArithmetic.toNat (d.stacks 14)=i)
    (hb : (d.stacks 5).length=b)
    (hacc : d.stacks 13=(rowPayload b m (prefixSlots m shifts Q side v a i)).reverse++tail) :
    portAccum d (decide (Q a ⟨i,hi⟩=1)) (decide (Q a ⟨i,hi⟩=2))
        (vertexPairs v (shifts ⟨i,hi⟩))=
      (rowPayload b m (prefixSlots m shifts Q side v a (i+1))).reverse++tail := by
  rw [portAccum_vertex d shifts Q side v a ⟨i,hi⟩ b hside hD hm hp hb,hacc,
    prefixSlots_succ m shifts Q side v a i hi,rowPayload_append,List.reverse_append]
  exact (List.append_assoc _ _ _).symm

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
