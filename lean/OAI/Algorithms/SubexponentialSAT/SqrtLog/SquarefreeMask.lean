import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

def encodeMask {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ s))

@[simp] theorem encodeMask_length {n : ℕ} (s : Finset (Fin n)) : (encodeMask s).length = n := by
  simp [encodeMask]

theorem encodeMask_union {n : ℕ} (s t : Finset (Fin n)) :
    List.zipWith (· || ·) (encodeMask s) (encodeMask t) = encodeMask (s ∪ t) := by
  apply List.ext_getElem
  · simp [encodeMask]
  · intro i hi hj
    simp [encodeMask]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
