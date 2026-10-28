import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace OAI.Algorithms

/-! Integer selection of a sufficient Hasse-jet order. -/

namespace SubexponentialSAT.SqrtLog.Reconstruction

/-- Uses integer division only; no analytic rounding operation is required. -/
def jetOrder (degreeBound nodeCount : ℕ) : ℕ := degreeBound / nodeCount + 1

theorem jetOrder_pos (degreeBound nodeCount : ℕ) :
    0 < jetOrder degreeBound nodeCount := Nat.succ_pos _

theorem degreeBound_lt (degreeBound nodeCount : ℕ) (hQ : 0 < nodeCount) :
    degreeBound < nodeCount * jetOrder degreeBound nodeCount := by
  exact Nat.lt_mul_div_succ degreeBound hQ

theorem natDegree_lt_jetOrder {A : Type*} [Semiring A]
    (target : Polynomial A) (degreeBound nodeCount : ℕ) (hQ : 0 < nodeCount)
    (hdegree : target.natDegree ≤ degreeBound) :
    target.natDegree < nodeCount * jetOrder degreeBound nodeCount :=
  hdegree.trans_lt (degreeBound_lt degreeBound nodeCount hQ)

/-- The marked-query allowance is explicit and does not multiply precision
by the number of hash factors. -/
def markedDegreeBound (width rowDegree hashes precision : ℕ) : ℕ :=
  width * rowDegree * (2 * hashes + 3 * (precision - 1) + 1)

theorem marked_degree_lt (width rowDegree hashes precision nodes : ℕ)
    (hQ : 0 < nodes) :
    markedDegreeBound width rowDegree hashes precision <
      nodes * jetOrder (markedDegreeBound width rowDegree hashes precision) nodes :=
  degreeBound_lt _ _ hQ

end SubexponentialSAT.SqrtLog.Reconstruction

end OAI.Algorithms
