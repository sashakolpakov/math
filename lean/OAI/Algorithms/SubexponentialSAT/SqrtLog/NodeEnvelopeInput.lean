import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePayload
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeInputs

namespace OAI.Algorithms

/-! Native input words bound the elementary preparation dimensions. The
proof applies also to the addressed (owner,n+factor) plan stream. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds

theorem selected_le_max_of_lt (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool)
    (z : ℕ) (hr : 0 < r) (hz : z < Q*r) :
    (selectedHeads n rows low z).length ≤ LayoutProducedHeads.maxSelected n Q r rows low := by
  let t : Fin Q := ⟨z/r,(Nat.div_lt_iff_lt_mul hr).mpr hz⟩
  let g : Fin r := ⟨z%r,Nat.mod_lt z hr⟩
  have h := LayoutProducedHeads.selected_le_max n Q r rows low t g
  have he : z/r*r+z%r=z := by simpa only [Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div z r
  simpa only [t,g,he] using h

theorem rows_length_le_flatten (rows : List (List Bool))
    (h : ∀ row∈rows,1 ≤ row.length) : rows.length ≤ rows.flatten.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun x hx=>h x (by simp [hx]))
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

theorem ready_preparation_bound (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ha : Native.Ready s a) (B : ℕ) (hb : WordBound B a) (hr : 0 < s.r)
    (z : ℕ) (hz : z ≤ s.Q*s.r) :
    preparationSize s.n s.N s.rows s.low (s.Q*s.r) z ≤ 7*B+2 := by
  have hn : s.n ≤ B := by simpa [ha.ambient,unary] using hb 128
  have hN : s.N ≤ B := by simpa [ha.factors,unary] using hb 129
  have hw : s.Q*s.r ≤ B := by simpa [ha.wordWidth,unary] using hb 132
  have hrows : s.rows.flatten.length ≤ B := by simpa [ha.words] using hb 133
  have hlow : s.low.length ≤ B := by simpa [ha.low] using hb 134
  have hQ : 0 < s.Q := by have := s.node.isLt; omega
  have hlen : s.rows.length ≤ B := (rows_length_le_flatten s.rows (by
    intro row hrow; rw [s.rows_width row hrow]; exact Nat.mul_pos hQ hr)).trans hrows
  unfold preparationSize
  omega

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
