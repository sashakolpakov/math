import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionRows

namespace OAI.Algorithms

/-! The outer triangular loop of the fixed convolution controller. Each row
copies the preserved right-hand array, consumes one left coefficient, and
executes only the still-relevant output positions. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def outerAfter (w : Buffers) (leftTail accumulator fuelTail : List Bool) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 leftTail)
    2 accumulator) 4 (false :: w 4)) 5 fuelTail

def outerCost (D W pairCost : ℕ) : ℕ :=
  (D + 1) * (pairCost + 100 * (W + 1))

/-- One actual row of the convolution, including preparation and cleanup. -/
theorem outerStep_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a : C) (rest Q acc : List C) (bit : Bool) (tokens : List Bool)
    (hQ : Q.length = D) (hlen : acc.length = D)
    (hleft : w 0 = encodeArray encode (a :: rest))
    (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
    (hcount : w 5 = bit :: tokens)
    (hindex : (w 4).length + (w 5).length ≤ D)
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (outerStep pair) (outerCost D W pairCost) (buffers base w)
      (buffers base (outerAfter w (encodeArray encode rest)
        (encodeArray encode (TruncatedConvolution.row add mul a (w 4).length
          (Q.take (w 5).length) acc)) tokens)) := by
  let r := (w 5).length
  let i := (w 4).length
  let w₁ := Function.update w 7 (w 5)
  let w₂ := Function.update w₁ 5 tokens
  let w₃ := Function.update (Function.update w₂ 0 (encodeArray encode rest)) 8 (encode a)
  let w₄ := Function.update w₃ 6 (encodeArray encode Q)
  let w₅ := Function.update w₄ 3 (w 4)
  let values := TruncatedConvolution.row add mul a i (Q.take r) acc
  let w₆ := innerDone w₅ (encodeArray encode values) (encodeArray encode (Q.drop r)) r
  let w₇ := Function.update w₆ 6 []
  let w₈ := Function.update w₇ 7 []
  let w₉ := Function.update w₈ 3 []
  let w₁₀ := Function.update w₉ 8 []
  let w₁₁ := Function.update w₁₀ 4 (false :: w₁₀ 4)
  have hrD : r ≤ D := by dsimp [r]; omega
  have hiD : i ≤ D := by dsimp [i]; omega
  have hQr : (Q.take r).length = r := by simp [List.length_take, hQ, Nat.min_eq_left hrD]
  have h₁ : ExecutesIn (copy 106 109) (7 * r + 5) (buffers base w) (buffers base w₁) := by
    simpa [w₁, r, buffers_update, bufferPorts, h7] using
      copy_run 106 109 (buffers base w) (by decide) (by decide) (by decide)
        (by simpa using h120)
  have h₂ : ExecutesIn (popToken 106) 1 (buffers base w₁) (buffers base w₂) := by
    simpa [w₂, buffers_update, bufferPorts] using
      popToken_run 106 (buffers base w₁) bit tokens (by simpa [w₁] using hcount)
  have h₃ : ExecutesIn (takeCell 100 110) (14 * W + 11)
      (buffers base w₂) (buffers base w₃) := by
    have ht := takeCell_run 100 110 (buffers base w₂) (encode a) (encodeArray encode rest)
      (by decide) (by simpa [w₂, w₁] using hleft)
      (by simpa using h121) (by simpa using h122) (by simpa [hencode] using hwidth)
    simpa [w₃, buffers_update, bufferPorts, w₂, w₁, h8, hencode] using ht
  have h₄ : ExecutesIn (copy 101 108) (7 * (D * W) + 5)
      (buffers base w₃) (buffers base w₄) := by
    have ht := copy_run 101 108 (buffers base w₃)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₄, buffers_update, bufferPorts, w₃, w₂, w₁, hright, h6,
      encodeArray_length encode W hencode, hQ] using ht
  have h₅ : ExecutesIn (copy 105 103) (7 * i + 5)
      (buffers base w₄) (buffers base w₅) := by
    have ht := copy_run 105 103 (buffers base w₄)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₅, i, buffers_update, bufferPorts, w₄, w₃, w₂, w₁, h3] using ht
  have h₆ : ExecutesIn (innerLoop pair) (r * (pairCost + 21 * W + 21) + 2)
      (buffers base w₅) (buffers base w₆) := by
    have ht := innerLoop_run pair base encode add mul D W pairCost hpair hencode hwidth
      h120 h121 h122 w₅ a acc (Q.take r) (Q.drop r) hlen
      (by simpa [w₅, w₄, w₃, w₂, w₁] using hacc)
      (by simp [w₅, w₄, List.take_append_drop])
      (by simp [w₅, w₄, w₃, w₂, w₁, hQr, r])
      (by simp [w₅, w₄, w₃])
      (by simpa [w₅, w₄, w₃, w₂, w₁] using h9)
      (by simpa [w₅, w₄, w₃, w₂, w₁] using h10)
      (by simpa [w₅, hQr, r] using hindex)
    have hi : (w₅ 3).length = (w 4).length := by
      simp [w₅, w₄]
    simpa [w₆, values, i, hQr, hi] using ht
  have h₇ : ExecutesIn (clear 108) (2 * (D * W) + 3)
      (buffers base w₆) (buffers base w₇) := by
    have ht := clear_run 108 (buffers base w₆)
    have he : (buffers base w₆ 108).length ≤ D * W := by
      have heq : buffers base w₆ 108 = encodeArray encode (Q.drop r) := by
        simp [w₆, innerDone]
      rw [heq, encodeArray_length encode W hencode, List.length_drop, hQ]
      exact Nat.mul_le_mul_right W (Nat.sub_le D r)
    have := ht.mono (Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 3)
    simpa [w₇, buffers_update, bufferPorts] using this
  have h₈ : ExecutesIn (clear 109) 3 (buffers base w₇) (buffers base w₈) := by
    simpa [w₈, buffers_update, bufferPorts, w₇, w₆, innerDone] using clear_run 109 (buffers base w₇)
  have h₉ : ExecutesIn (clear 103) (2 * D + 3) (buffers base w₈) (buffers base w₉) := by
    have ht := clear_run 103 (buffers base w₈)
    have he : (buffers base w₈ 103).length ≤ D := by
      simpa [w₈, w₇, w₆, innerDone, w₅, r, Nat.add_comm] using hindex
    have := ht.mono (Nat.add_le_add_right (Nat.mul_le_mul_left 2 he) 3)
    simpa [w₉, buffers_update, bufferPorts] using this
  have h₁₀ : ExecutesIn (clear 110) (2 * W + 3) (buffers base w₉) (buffers base w₁₀) := by
    simpa [w₁₀, buffers_update, bufferPorts, w₉, w₈, w₇, w₆, innerDone,
      w₅, w₄, w₃, hencode] using clear_run 110 (buffers base w₉)
  have h₁₁ : ExecutesIn (appendIndex 105) 2 (buffers base w₁₀) (buffers base w₁₁) := by
    simpa only [w₁₁, buffers_update, show bufferPorts 4 = (105 : Fin 256) from rfl,
      buffers_105] using appendIndex_run 105 (buffers base w₁₀)
  have hfinal : w₁₁ = outerAfter w (encodeArray encode rest) (encodeArray encode values) tokens := by
    funext j
    fin_cases j <;> simp [w₁₁, w₁₀, w₉, w₈, w₇, w₆, innerDone, w₅, w₄, w₃,
      w₂, w₁, outerAfter, h3, h6, h7, h8]
  have ht := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq
    (h₇.seq (h₈.seq (h₉.seq (h₁₀.seq h₁₁)))))))))
  rw [hfinal] at ht
  change ExecutesIn (outerStep pair) _ _ _ at ht
  apply ht.mono
  have hrow := Nat.mul_le_mul_right (pairCost + 21 * W + 21) hrD
  dsimp [outerCost]
  nlinarith


structure OuterGood (base : Store) (encode : C → List Bool) (add mul : C → C → C)
    (Q : List C) (D : ℕ) (original : Buffers) (target : List C) (total : ℕ)
    (r : RowData C) (fuel : ℕ) (stk : Store) : Prop where
  store_eq : stk = buffers base r.work
  pending_length : r.pending.length = fuel
  values_length : r.values.length = D
  left : r.work 0 = encodeArray encode r.pending
  right : r.work 1 = encodeArray encode Q
  accumulator : r.work 2 = encodeArray encode r.values
  row_count : (r.work 5).length = fuel
  index_empty : r.work 3 = []
  right_empty : r.work 6 = []
  count_empty : r.work 7 = []
  coefficient_empty : r.work 8 = []
  operand_left : r.work 9 = []
  operand_right : r.work 10 = []
  index_bound : (r.work 4).length + fuel ≤ D
  index_tokens : List.replicate fuel false ++ r.work 4 =
    List.replicate total false ++ original 4
  target_eq : TruncatedConvolution.rows add mul Q (r.work 4).length fuel r.pending r.values = target

def outerDone (w : Buffers) (target : List Bool) (count : ℕ) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 []) 2 target)
    4 (List.replicate count false ++ w 4)) 5 []

/-- Actual execution of all remaining triangular rows. The proof invariant
tracks the remaining value computation and the physical unary counters. -/
theorem outerLoop_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q acc : List C) (hQ : Q.length = D) (hlen : acc.length = D)
    (hleft : w 0 = encodeArray encode P) (hright : w 1 = encodeArray encode Q)
    (hacc : w 2 = encodeArray encode acc) (hcount : (w 5).length = P.length)
    (hindex : (w 4).length + P.length ≤ D)
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (outerLoop pair) (P.length * (outerCost D W pairCost + 2) + 2)
      (buffers base w) (buffers base (outerDone w
        (encodeArray encode (TruncatedConvolution.rows add mul Q (w 4).length P.length P acc))
        P.length)) := by
  let target := TruncatedConvolution.rows add mul Q (w 4).length P.length P acc
  let Good := OuterGood base encode add mul Q D w target P.length
  let Inv : ℕ → Store → Prop := fun fuel stk => ∃ r, Good r fuel stk
  have hInvCount : ∀ fuel stk, Inv fuel stk → (stk 106).length = fuel := by
    intro fuel stk h
    obtain ⟨r, hr⟩ := h
    rw [hr.store_eq, buffers_106]
    exact hr.row_count
  have hStep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval (outerStep pair) n d e ∧ n ≤ outerCost D W pairCost ∧
        Inv fuel e.stacks := by
    intro fuel d hd
    obtain ⟨r, hr⟩ := hd
    have hpending := hr.pending_length
    cases hlist : r.pending with
    | nil => simp [hlist] at hpending
    | cons a rest =>
      have hrest : rest.length = fuel := by simpa [hlist] using hpending
      have hcnt := hr.row_count
      cases htokens : r.work 5 with
      | nil => simp [htokens] at hcnt
      | cons bit tokens =>
        have htlen : tokens.length = fuel := by simpa [htokens] using hcnt
        let values' := TruncatedConvolution.row add mul a (r.work 4).length (Q.take (fuel + 1)) r.values
        let work' := outerAfter r.work (encodeArray encode rest) (encodeArray encode values') tokens
        let r' : RowData C := ⟨work', values', rest⟩
        have hrun := outerStep_run pair base encode add mul D W pairCost hpair hencode
          hwidth h120 h121 h122 r.work a rest Q r.values bit tokens hQ hr.values_length
          (by simpa [hlist] using hr.left) hr.right hr.accumulator htokens
          (by simpa [hr.row_count] using hr.index_bound)
          hr.index_empty hr.right_empty hr.count_empty hr.coefficient_empty
          hr.operand_left hr.operand_right
        obtain ⟨n, regs', hn, he⟩ := hrun d.regs
        have hdEq : d = ⟨d.regs, buffers base r.work⟩ :=
          SubexpScanPrimitives.state_ext rfl hr.store_eq
        refine ⟨n, ⟨regs', buffers base work'⟩, ?_, hn, r', ?_⟩
        · rw [← hdEq] at he
          simpa only [hr.row_count] using he
        · refine {
            store_eq := rfl
            pending_length := hrest
            values_length := ?_
            left := ?_
            right := ?_
            accumulator := ?_
            row_count := ?_
            index_empty := ?_
            right_empty := ?_
            count_empty := ?_
            coefficient_empty := ?_
            operand_left := ?_
            operand_right := ?_
            index_bound := ?_
            index_tokens := ?_
            target_eq := ?_ }
          · simpa [r', values'] using hr.values_length
          · simp [r', work', outerAfter]
          · simpa [r', work', outerAfter] using hr.right
          · simp [r', work', outerAfter]
          · simpa [r', work', outerAfter] using htlen
          · simpa [r', work', outerAfter] using hr.index_empty
          · simpa [r', work', outerAfter] using hr.right_empty
          · simpa [r', work', outerAfter] using hr.count_empty
          · simpa [r', work', outerAfter] using hr.coefficient_empty
          · simpa [r', work', outerAfter] using hr.operand_left
          · simpa [r', work', outerAfter] using hr.operand_right
          · have hbound := hr.index_bound
            simp only [r', work', outerAfter, Function.update_of_ne (by decide : (4 : Fin 11) ≠ 5),
              Function.update_self, List.length_cons]
            omega
          · have hsame : List.replicate fuel false ++ (false :: r.work 4) =
                List.replicate (fuel + 1) false ++ r.work 4 := by
              simp [List.replicate_add, List.append_assoc]
            simpa [r', work', outerAfter, hsame] using hr.index_tokens
          · simpa [r', work', outerAfter, values', hlist, TruncatedConvolution.rows] using hr.target_eq
  intro regs
  have hInitial : Inv P.length (buffers base w) := by
    refine ⟨⟨w, acc, P⟩, ?_⟩
    exact {
      store_eq := rfl, pending_length := rfl, values_length := hlen,
      left := hleft, right := hright, accumulator := hacc, row_count := hcount,
      index_empty := h3, right_empty := h6, count_empty := h7, coefficient_empty := h8,
      operand_left := h9, operand_right := h10, index_bound := hindex,
      index_tokens := rfl, target_eq := rfl }
  obtain ⟨n, e, he, hn, r, hr⟩ := unaryRun_eval 106 14 (outerStep pair) Inv
    (fun _ => outerCost D W pairCost) hInvCount hStep P.length
    ⟨regs, buffers base w⟩ hInitial
  have hnil : r.pending = [] := List.length_eq_zero_iff.mp hr.pending_length
  have hvalues : r.values = target := by simpa [TruncatedConvolution.rows] using hr.target_eq
  have htokens : r.work 5 = [] := List.length_eq_zero_iff.mp hr.row_count
  have hwork : r.work = outerDone w (encodeArray encode target) P.length := by
    funext j
    fin_cases j
    · simpa [outerDone, hnil] using hr.left
    · simpa [outerDone, hright] using hr.right
    · simpa [outerDone, hvalues] using hr.accumulator
    · simpa [outerDone, h3] using hr.index_empty
    · simpa [outerDone] using hr.index_tokens
    · simpa [outerDone] using htokens
    · simpa [outerDone, h6] using hr.right_empty
    · simpa [outerDone, h7] using hr.count_empty
    · simpa [outerDone, h8] using hr.coefficient_empty
    · simpa [outerDone, h9] using hr.operand_left
    · simpa [outerDone, h10] using hr.operand_right
  have hstack : e.stacks = buffers base (outerDone w (encodeArray encode target) P.length) := by
    rw [hr.store_eq, hwork]
  have heEq : e = ⟨e.regs, buffers base (outerDone w (encodeArray encode target) P.length)⟩ :=
    SubexpScanPrimitives.state_ext rfl hstack
  have hbudget := unaryBudget_le (fun _ => outerCost D W pairCost)
    (outerCost D W pairCost) P.length (by intros; rfl)
  refine ⟨n, e.regs, ?_, ?_⟩
  · omega
  · change Eval (outerLoop pair) n ⟨regs, buffers base w⟩ e at he
    rw [heEq] at he
    exact he

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
