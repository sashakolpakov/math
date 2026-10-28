import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeColumns
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQueryInventory

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds LeafProgram.NodeNative

 theorem row_outside (rows : List (List Bool)) (z : ℕ)
    (hw : ∀ row∈rows,row.length ≤ z) (j : ℕ) : (rows.getD j []).getD z false=false := by
  induction rows generalizing j with
  | nil => simp
  | cons row rows ih =>
    cases j with
    | zero =>
      change row.getD z false=false
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (hw row (by simp)),Option.getD_none]
    | succ j =>
      simpa only [List.getD_cons_succ] using ih (fun r hr=>hw r (by simp [hr])) j

 theorem selected_outside (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ)
    (hw : ∀ row∈rows,row.length ≤ z) : selectedHeads n rows low z=[] := by
  simp only [selectedHeads,HeadIdentifierProgram.chosenIds,HeadIdentifierProgram.predicate,
    List.filter_eq_nil_iff, Bool.and_eq_true]
  intro j hj
  simp only [row_outside rows z hw j, Bool.false_eq_true, and_false, not_false_eq_true]

 theorem selected_le_max (s : Native.Inputs) (hr : 0 < s.r) (z : ℕ) :
    (selectedHeads s.n s.rows s.low z).length ≤
      LayoutProducedHeads.maxSelected s.n s.Q s.r s.rows s.low := by
  by_cases hz : z < s.Q*s.r
  · exact NodeEnvelope.selected_le_max_of_lt _ _ _ _ _ _ hr hz
  · rw [selected_outside s.n s.rows s.low z (by intro row hrow; rw [s.rows_width row hrow]; omega)]
    simp

 def headModel (Z : ℕ) : ℕ :=
  20000*(Z+1)^4+
    (Z*(100000000*(traceStepCap (2*(Z+1)^2+3) Z Z Z Z Z Z+1)^4+2)+2)+
    (100000+1007*10000)*(traceStateCap (2*(Z+1)^2+3) Z Z Z Z Z+1)^2+1

 theorem headBudget_le_model (s : HeadInputs) (B rCap S E K Z : ℕ)
    (hb : B ≤ Z) (hr : rCap ≤ Z) (hs : S ≤ Z) (he : E ≤ Z) (hk : K ≤ Z)
    (hn : s.n ≤ Z) (hd : s.D ≤ Z) : headBudget s B rCap S E K ≤ headModel Z := by
  have hc : LeafHeadSetupProgram.cleanupPorts.length ≤ 10000 := by
    simp only [LeafHeadSetupProgram.cleanupPorts, List.length_append,
      LeafHeadSetupProgram.workPorts, LeafHeadSetupProgram.privatePorts,
      List.length_ofFn]
    norm_num
  unfold headBudget headModel traceStepCap traceStateCap payloadWidth
  gcongr

 theorem headModel_le (Z : ℕ) (hZ : 1 ≤ Z) : headModel Z ≤ 100000000000000000000000000000000000000000000000000*Z^17 := by
  have hp (j : ℕ) (hj : j ≤ 17) : Z^j ≤ Z^17 := Nat.pow_le_pow_right hZ hj
  have h0 : 1 ≤ Z^17 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^17 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  have h10 := hp 10 (by decide)
  have h11 := hp 11 (by decide)
  have h12 := hp 12 (by decide)
  have h13 := hp 13 (by decide)
  have h14 := hp 14 (by decide)
  have h15 := hp 15 (by decide)
  have h16 := hp 16 (by decide)
  have h17 := hp 17 (by decide)
  dsimp only [headModel,traceStepCap,traceStateCap,payloadWidth]
  conv_lhs => ring_nf
  omega

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
