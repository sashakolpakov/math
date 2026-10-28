import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionSelectorCostJoin

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.SelectorCost
open Statement Filter Asymptotic
open scoped Topology

/-- A measured source can be smaller than the full cap (for example because
its immutable count word is shorter than V). All constants precede inputs. -/
theorem eventually_source_runtime (C d q p : ℕ) {Ct At : ℝ}
    (hCt : 0 ≤ Ct) (dt : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W V width X : ℕ,
      m ≤ n*B → B ≤ L n^q → V ≤ initialSize C d q p n W → width ≤ V →
      X ≤ physicalSource V width (SparseCode.distanceDenom m B) (HashSelect.loopCap n m) m →
      runtimeBound Ct At dt X n ≤
        runtimeBound (Ct*400^dt) (At+(dt:ℝ)*2) ((p+1)*dt) W n := by
  filter_upwards [eventually_physicalSource C d q p] with n hn
  intro m B W V width X hm hB hV hw hX
  have hs := hn m B W V width hm hB hV hw
  have hx : (X:ℝ)+1 ≤ runtimeBound 400 2 (p+1) W n := by
    have hX' : (X : ℝ) ≤ physicalSource V width
        (SparseCode.distanceDenom m B) (HashSelect.loopCap n m) m := by
      exact_mod_cast hX
    linarith
  exact FinalCost.runtimeBound_substitute hCt dt (p+1) W X n hx

/-- Specialization to the already-certified full-history coefficient. -/
theorem eventually_history_source_bound (C d q p : ℕ) {Cq Aq : ℝ}
    (hCq : 0 ≤ Cq) (dq : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m B W V width X : ℕ,
      m ≤ n*B → B ≤ L n^q → V ≤ initialSize C d q p n W → width ≤ V →
      X ≤ physicalSource V width (SparseCode.distanceDenom m B) (HashSelect.loopCap n m) m →
      runtimeBound (3000000*4^8*Cq) (16+Aq) (8+dq) X n ≤
        runtimeBound ((3000000*4^8*Cq)*400^(8+dq))
          (16+Aq+((8+dq:ℕ):ℝ)*2) ((p+1)*(8+dq)) W n := by
  exact eventually_source_runtime C d q p (by positivity) (8+dq)

end SubexponentialSAT.SqrtLog.Execution.SelectorCost

end OAI.Algorithms
