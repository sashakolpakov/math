import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerResources
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramCostPolynomial

namespace OAI.Algorithms

/-! The produced bucket bytes are bounded independently of any surrounding
Cartesian tuple stream. The actual bucket writer pays for all output bits. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

theorem tableOutput_length_le_cost (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) :
    (Controller.tableOutput (Controller.labelledRecords W rows js n h)).length ≤
      Controller.cost W rows js n h := by
  unfold Controller.cost Controller.groupCost SubexponentialSAT.Subexp.PackingBucketTable.budget
    Controller.tableOutput
  omega

theorem tableOutput_length_le (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h B : ℕ) (hw : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    (Controller.tableOutput (Controller.labelledRecords W rows js n h)).length ≤
      139024*(2^h+1)^2*(h+rows.length+B+n+W.length+2)^6 := by
  exact (tableOutput_length_le_cost W rows js n h).trans
    ((Cost.controller_cost_bound W rows js n h B hw hb hlen hjs).trans
      (Cost.total_coarse W h rows.length B n))

theorem signed_tableOutput_length_le (W : List Bool) (rows : List (List SignedWord))
    (shifted : List (List (List Bool))) (js : List ℕ) (n h L : ℕ)
    (hr : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows shifted)
    (hW : W.length ≤ L) (hw : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    (Controller.tableOutput (Controller.labelledRecords W shifted js n h)).length ≤
      101358497*(2^h+1)^2*(h+rows.length+L+n+W.length+2)^6 := by
  have ht := tableOutput_length_le_cost W shifted js n h
  have hc := preprocess_controller_cost_le W rows shifted js n h L hr hW hw hb hlen hjs
  exact (show (Controller.tableOutput (Controller.labelledRecords W shifted js n h)).length ≤
    Cost.signedTotal W h rows.length L n by omega).trans (Cost.signedTotal_coarse W h rows.length L n)

end SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

end OAI.Algorithms
