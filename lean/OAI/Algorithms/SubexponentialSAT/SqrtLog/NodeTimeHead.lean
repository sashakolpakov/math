import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeHeadModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds LeafProgram.NodeNative
open ProducedQueryResources MulticolorTypes

noncomputable def headCap (B W : ℕ) : ℕ := 10^120*(B+2)^48*(W+1)^2

theorem headCap_bounds (B W : ℕ) :
    7*B+2 ≤ headCap B W ∧ W ≤ headCap B W ∧ 1 ≤ headCap B W := by
  have hb : B+2 ≤ (B+2)^48 := by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ B+2) (show 1 ≤ 48 by decide)
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  have hc : 10 ≤ 10^120 := by norm_num
  have hB : 10*(B+2) ≤ headCap B W := by
    unfold headCap
    calc
      _ = 10*(B+2)*1 := by ring
      _ ≤ _ := by gcongr ; omega
  have hW : W+1 ≤ headCap B W := by
    unfold headCap
    calc
      _ = 1*1*(W+1) := by ring
      _ ≤ _ := by gcongr <;> omega
  omega

theorem matrix_le_headCap (s : Native.Inputs) (B W : ℕ) (h : InputBounds s B)
    (word : List Bool) (hw : word.length ≤ B) (z : ℕ)
    (hh : 2^(selectedHeads s.n s.rows s.low z).length ≤ W) :
    matrixEnvelope word s.columnTime s.columnLength s.D s.n
      (selectedHeads s.n s.rows s.low z).length ≤ headCap B W := by
  have hc := (columns_le h).1.trans (columnEnvelope_le (B+1))
  norm_num only [Nat.add_assoc] at hc
  have hl := (columns_le h).2
  have hn := selectedHeads_length s.n s.rows s.low z
  have hp : B+2 ≤ (B+2)^8 := by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ B+2) (show 1 ≤ 8 by decide)
  have hp3 : (B+2)^3 ≤ (B+2)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hl' : s.columnLength ≤ 102*(B+2)^8 := by
    calc
      _ ≤ (B+1)*(100*(B+2)^2+2) := hl
      _ ≤ 102*(B+2)^3 := by nlinarith only [Nat.zero_le B]
      _ ≤ _ := Nat.mul_le_mul_left _ hp3
  have hs : matrixSize word s.columnTime s.columnLength s.D s.n
      (selectedHeads s.n s.rows s.low z).length ≤ 10^18*(B+2)^8 := by
    unfold matrixSize
    have hd := h.D
    have hnn := h.n
    norm_num only [show (10:ℕ)^18=1000000000000000000 from rfl]
    omega
  unfold matrixEnvelope headCap
  calc
    _ ≤ 200000000*(W+1)^2*(10^18*(B+2)^8)^6 := by gcongr
    _ ≤ 10^120*(B+2)^48*(W+1)^2 := by
      have hcoef : 200000000*(10:ℕ)^(18*6) ≤ 10^120 := by norm_num
      calc
        _ = (200000000*10^(18*6))*((B+2)^48*(W+1)^2) := by ring
        _ ≤ 10^120*((B+2)^48*(W+1)^2) := Nat.mul_le_mul_right _ hcoef
        _ = _ := by ring

/-- All retained incidence rows and integer coefficients are paid by physical
input words. The head enumeration itself is paid by assembled work. -/
theorem query_head_bound (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {a b : LeafProgram.NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (B : ℕ) (hb : WordBound B a) :
    pr.head.steps ≤ 10^50*(headCap B
      (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)))^17 := by
  let s := Native.queryInputsAddressed query k hg first tail node
  let p := resources query k occurrence qi hg first tail
  let W := CostAssembly.assembledWork k (ambient query) p
  have hload := loaded_wordBound ha B hb
  have hbounds := inputBounds s (Native.project (loadedState a)) ha.heads B (fun i=>hload i)
  have hr : 0 < s.r := (problem query k hg).hr
  have hc := headCap_bounds B W
  have hQ := hbounds.Qr
  have hn := hbounds.n
  have hD := hbounds.D
  have hS := NodeEnvelope.ready_preparation_bound s (Native.project (loadedState a)) ha.heads B (fun i=>hload i) hr
  have hbase : 0 < p.labelBase := by change 0 < 2*ambient query*matrixHeight query k+1; omega
  have hheads : 1 ≤ p.heads := make_heads_pos query k occurrence _ _ _ _ _ _
  have hbits : 1 ≤ p.bits := make_bits_pos query k occurrence _ _ _ _ _ _
  have hexp := CostAssembly.headAssignments_le_assembledWork k (ambient query) p hbase hheads hbits
  have hE : ∀ z ≤ s.Q*s.r, matrixEnvelope ((loadedState a).stacks 141)
      s.columnTime s.columnLength s.D s.n (selectedHeads s.n s.rows s.low z).length ≤ headCap B W := by
    intro z hz
    apply matrix_le_headCap s B W hbounds _ (hload 141) z
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (selected_le_max s hr z)).trans hexp
  have haddress : s.node.val*s.r+s.r ≤ s.Q*s.r := by nlinarith [s.node.isLt]
  have ht := pr.head_budget_le ha B (s.Q*s.r) (7*B+2) (headCap B W) W hb haddress
    (NodeEnvelope.query_inventory_bound query k occurrence qi hg first tail node pr ha) hS hE
  apply ht.trans
  apply (headBudget_le_model s B (s.Q*s.r) (7*B+2) (headCap B W) W (headCap B W)
    (by omega) (by omega) hc.1 le_rfl hc.2.1 (by omega) (by omega)).trans
  exact headModel_le _ hc.2.2

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
