import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseProduct
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

def encodeIndex {n : ℕ} (a : Index (Fin n)) : List Bool :=
  Encoding.encodeNat a.u ++ Encoding.encodeNat a.z ++ encodeMask a.vars

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

@[simp] theorem encodeIndex_length {n : ℕ} (a : Index (Fin n)) :
    (encodeIndex a).length = a.u + a.z + n + 2 := by
  simp [encodeIndex]
  omega

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

theorem encodeIndex_join {n : ℕ} (a b : Index (Fin n)) :
    encodeIndex (a.join b) =
      Encoding.encodeNat (a.u + b.u) ++ Encoding.encodeNat (a.z + b.z) ++
        List.zipWith (· || ·) (encodeMask a.vars) (encodeMask b.vars) := by
  rw [encodeMask_union]
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
