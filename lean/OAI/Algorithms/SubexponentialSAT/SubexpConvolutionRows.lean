import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionIteration

namespace OAI.Algorithms

/-! The triangular convolution controller charges actual fixed-width reads,
copies, and cell writes. The local pair contract is a contract for a fixed
finite command and is instantiated by the concrete quartic/jet service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def encodeArray (encode : C → List Bool) (xs : List C) : List Bool :=
  (xs.map encode).flatten

@[simp] theorem encodeArray_nil (encode : C → List Bool) : encodeArray encode [] = [] := rfl
@[simp] theorem encodeArray_cons (encode : C → List Bool) (a : C) (xs : List C) :
    encodeArray encode (a :: xs) = encode a ++ encodeArray encode xs := by simp [encodeArray]

@[simp] theorem encodeArray_append (encode : C → List Bool) (xs ys : List C) :
    encodeArray encode (xs ++ ys) = encodeArray encode xs ++ encodeArray encode ys := by
  simp [encodeArray]

theorem encodeArray_length (encode : C → List Bool) (W : ℕ)
    (hW : ∀ x, (encode x).length = W) (xs : List C) :
    (encodeArray encode xs).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, hW, Nat.succ_mul, Nat.add_comm]

/-- An actual pair-command contract. Only one local multiply-and-accumulate
operation is assumed here, at an in-bounds output cell, with explicit cost. -/
def PairSpec (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D pairCost : ℕ) : Prop :=
  ∀ (w : Buffers) (a b : C) (acc : List C), acc.length = D →
    (w 3).length < D → w 2 = encodeArray encode acc →
    w 9 = encode a → w 10 = encode b →
    ExecutesIn pair pairCost (buffers base w)
      (buffers base (Function.update (Function.update (Function.update w 9 []) 10 []) 2
        (encodeArray encode (TruncatedConvolution.addProduct add mul (w 3).length a b acc))))

def innerAfter (w : Buffers) (accumulator rightTail cellsLeft : List Bool) : Buffers :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update w 7 cellsLeft) 6 rightTail) 9 []) 10 []) 2 accumulator)
    3 (false :: w 3)

/-- One iteration of the actual inner command, including every data movement
and the physical increment of the output index. -/
theorem innerStep_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a b : C) (acc : List C) (rightTail cellsLeft : List Bool) (bit : Bool)
    (ha : (encode a).length = W) (hb : (encode b).length = W)
    (hlen : acc.length = D) (hi : (w 3).length < D)
    (hacc : w 2 = encodeArray encode acc) (hright : w 6 = encode b ++ rightTail)
    (hcount : w 7 = bit :: cellsLeft) (hcoef : w 8 = encode a)
    (hx : w 9 = []) (hy : w 10 = []) :
    ExecutesIn (innerStep pair) (pairCost + 21 * W + 19) (buffers base w)
      (buffers base (innerAfter w
        (encodeArray encode (TruncatedConvolution.addProduct add mul (w 3).length a b acc))
        rightTail cellsLeft)) := by
  let w₁ := Function.update w 7 cellsLeft
  let w₂ := Function.update (Function.update w₁ 6 rightTail) 10 (encode b)
  let w₃ := Function.update w₂ 9 (encode a)
  let acc' := TruncatedConvolution.addProduct add mul (w 3).length a b acc
  let w₄ := Function.update (Function.update (Function.update w₃ 9 []) 10 []) 2
    (encodeArray encode acc')
  let w₅ := Function.update w₄ 3 (false :: w₄ 3)
  have h₁ : ExecutesIn (popToken 109) 1 (buffers base w) (buffers base w₁) := by
    simpa only [w₁, buffers_update, show bufferPorts 7 = (109 : Fin 256) from rfl] using
      popToken_run 109 (buffers base w) bit cellsLeft (by simpa using hcount)
  have h₂ : ExecutesIn (takeCell 108 199) (14 * W + 11)
      (buffers base w₁) (buffers base w₂) := by
    have h := takeCell_run 108 199 (buffers base w₁) (encode b) rightTail
      (by decide) (by simpa [w₁] using hright)
      (by simpa using h121) (by simpa using h122) (by simpa [hb] using hwidth)
    simpa [w₂, buffers_update, bufferPorts, w₁, hy, hb] using h
  have h₃ : ExecutesIn (copy 110 198) (7 * W + 5) (buffers base w₂) (buffers base w₃) := by
    have h := copy_run 110 198 (buffers base w₂)
      (by decide) (by decide) (by decide) (by simpa using h120)
    simpa [w₃, buffers_update, bufferPorts, w₂, w₁, hcoef, hx, ha] using h
  have h₄ : ExecutesIn pair pairCost (buffers base w₃) (buffers base w₄) := by
    have h := hpair w₃ a b acc hlen (by simpa [w₃, w₂, w₁] using hi)
      (by simpa [w₃, w₂, w₁] using hacc) (by simp [w₃]) (by simp [w₃, w₂])
    simpa [w₄, acc', w₃, w₂, w₁] using h
  have h₅ : ExecutesIn (appendIndex 103) 2 (buffers base w₄) (buffers base w₅) := by
    simpa only [w₅, buffers_update, show bufferPorts 3 = (103 : Fin 256) from rfl,
      buffers_103] using appendIndex_run 103 (buffers base w₄)
  have hfinal : w₅ = innerAfter w (encodeArray encode acc') rightTail cellsLeft := by
    funext j
    fin_cases j <;> simp [w₅, w₄, w₃, w₂, w₁, innerAfter]
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  rw [hfinal] at h
  change ExecutesIn (innerStep pair) _ _ _ at h
  convert h using 1
  omega

structure RowData (C : Type*) where
  work : Buffers
  values : List C
  pending : List C

structure InnerGood (base : Store) (encode : C → List Bool) (add mul : C → C → C)
    (a : C) (D : ℕ) (original : Buffers) (target suffix : List C) (total : ℕ)
    (r : RowData C) (fuel : ℕ) (stk : Store) : Prop where
  store_eq : stk = buffers base r.work
  pending_length : r.pending.length = fuel
  values_length : r.values.length = D
  accumulator : r.work 2 = encodeArray encode r.values
  right_tail : r.work 6 = encodeArray encode (r.pending ++ suffix)
  count_length : (r.work 7).length = fuel
  coefficient : r.work 8 = encode a
  operand_left : r.work 9 = []
  operand_right : r.work 10 = []
  index_bound : (r.work 3).length + fuel ≤ D
  index_tokens : List.replicate fuel false ++ r.work 3 =
    List.replicate total false ++ original 3
  target_eq : TruncatedConvolution.row add mul a (r.work 3).length r.pending r.values = target
  frame_left : r.work 0 = original 0
  frame_right : r.work 1 = original 1
  frame_row_index : r.work 4 = original 4
  frame_row_count : r.work 5 = original 5

def innerDone (w : Buffers) (target suffix : List Bool) (count : ℕ) : Buffers :=
  Function.update (Function.update
    (Function.update (Function.update w 2 target) 3 (List.replicate count false ++ w 3))
    6 suffix) 7 []

/-- The complete inner loop executes exactly the triangular row, with all
field data, scratch use, and per-pair work accounted for by actual commands. -/
theorem innerLoop_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (a : C) (acc pending suffix : List C)
    (hlen : acc.length = D) (hacc : w 2 = encodeArray encode acc)
    (hright : w 6 = encodeArray encode (pending ++ suffix))
    (hcount : (w 7).length = pending.length) (hcoef : w 8 = encode a)
    (hx : w 9 = []) (hy : w 10 = [])
    (hi : (w 3).length + pending.length ≤ D) :
    ExecutesIn (innerLoop pair) (pending.length * (pairCost + 21 * W + 21) + 2)
      (buffers base w) (buffers base (innerDone w
        (encodeArray encode (TruncatedConvolution.row add mul a (w 3).length pending acc))
        (encodeArray encode suffix) pending.length)) := by
  let target := TruncatedConvolution.row add mul a (w 3).length pending acc
  let Good := InnerGood base encode add mul a D w target suffix pending.length
  let Inv : ℕ → Store → Prop := fun fuel stk => ∃ r, Good r fuel stk
  have hInvCount : ∀ fuel stk, Inv fuel stk → (stk 109).length = fuel := by
    intro fuel stk h
    obtain ⟨r, hr⟩ := h
    rw [hr.store_eq, buffers_109]
    exact hr.count_length
  have hStep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval (innerStep pair) n d e ∧ n ≤ pairCost + 21 * W + 19 ∧
        Inv fuel e.stacks := by
    intro fuel d hd
    obtain ⟨r, hr⟩ := hd
    have hbs := hr.pending_length
    cases hlist : r.pending with
    | nil => simp [hlist] at hbs
    | cons b bs =>
      have hbsLen : bs.length = fuel := by simpa [hlist] using hbs
      have hcnt := hr.count_length
      cases htokens : r.work 7 with
      | nil => simp [htokens] at hcnt
      | cons bit tokens =>
        have htlen : tokens.length = fuel := by simpa [htokens] using hcnt
        let values' := TruncatedConvolution.addProduct add mul (r.work 3).length a b r.values
        let work' := innerAfter r.work (encodeArray encode values')
          (encodeArray encode (bs ++ suffix)) tokens
        let r' : RowData C := ⟨work', values', bs⟩
        have hrun := innerStep_run pair base encode add mul D W pairCost hpair hwidth h120 h121 h122
          r.work a b r.values (encodeArray encode (bs ++ suffix)) tokens bit
          (hencode a) (hencode b) hr.values_length (by have := hr.index_bound; omega)
          hr.accumulator (by simpa [hlist] using hr.right_tail) htokens hr.coefficient
          hr.operand_left hr.operand_right
        obtain ⟨n, regs', hn, he⟩ := hrun d.regs
        have hdEq : d = ⟨d.regs, buffers base r.work⟩ := by
          exact SubexpScanPrimitives.state_ext rfl hr.store_eq
        refine ⟨n, ⟨regs', buffers base work'⟩, ?_, hn, r', ?_⟩
        · rw [← hdEq] at he
          exact he
        · refine {
            store_eq := rfl
            pending_length := hbsLen
            values_length := ?_
            accumulator := ?_
            right_tail := ?_
            count_length := ?_
            coefficient := ?_
            operand_left := ?_
            operand_right := ?_
            index_bound := ?_
            index_tokens := ?_
            target_eq := ?_
            frame_left := ?_
            frame_right := ?_
            frame_row_index := ?_
            frame_row_count := ?_ }
          · simpa [r', values'] using hr.values_length
          · simp [r', work', innerAfter]
          · simp [r', work', innerAfter]
          · simpa [r', work', innerAfter] using htlen
          · simpa [r', work', innerAfter] using hr.coefficient
          · simp [r', work', innerAfter]
          · simp [r', work', innerAfter]
          · have hbound := hr.index_bound
            simp only [r', work', innerAfter, Function.update_self,
              List.length_cons]
            omega
          · have hsame : List.replicate fuel false ++ (false :: r.work 3) =
                List.replicate (fuel + 1) false ++ r.work 3 := by
              simp [List.replicate_add, List.append_assoc]
            simpa [r', work', innerAfter, hsame] using hr.index_tokens
          · simpa [r', work', innerAfter, values', hlist, TruncatedConvolution.row] using hr.target_eq
          · simpa [r', work', innerAfter] using hr.frame_left
          · simpa [r', work', innerAfter] using hr.frame_right
          · simpa [r', work', innerAfter] using hr.frame_row_index
          · simpa [r', work', innerAfter] using hr.frame_row_count
  intro regs
  have hInitial : Inv pending.length (buffers base w) := by
    refine ⟨⟨w, acc, pending⟩, ?_⟩
    exact {
      store_eq := rfl, pending_length := rfl, values_length := hlen,
      accumulator := hacc, right_tail := hright, count_length := hcount,
      coefficient := hcoef, operand_left := hx, operand_right := hy,
      index_bound := hi, index_tokens := rfl, target_eq := rfl,
      frame_left := rfl, frame_right := rfl, frame_row_index := rfl, frame_row_count := rfl }
  obtain ⟨n, e, he, hn, r, hr⟩ := unaryRun_eval 109 15 (innerStep pair) Inv
    (fun _ => pairCost + 21 * W + 19) hInvCount hStep pending.length
    ⟨regs, buffers base w⟩ hInitial
  have hnil : r.pending = [] := List.length_eq_zero_iff.mp hr.pending_length
  have hvalues : r.values = target := by simpa [hnil, TruncatedConvolution.row] using hr.target_eq
  have htokens : r.work 7 = [] := List.length_eq_zero_iff.mp hr.count_length
  have hwork : r.work = innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length := by
    funext j
    fin_cases j
    · simpa [innerDone] using hr.frame_left
    · simpa [innerDone] using hr.frame_right
    · simpa [innerDone, hvalues] using hr.accumulator
    · simpa [innerDone] using hr.index_tokens
    · simpa [innerDone] using hr.frame_row_index
    · simpa [innerDone] using hr.frame_row_count
    · simpa [innerDone, hnil] using hr.right_tail
    · simpa [innerDone] using htokens
    · simpa [innerDone, hcoef] using hr.coefficient
    · simpa [innerDone, hx] using hr.operand_left
    · simpa [innerDone, hy] using hr.operand_right
  have hstack : e.stacks = buffers base
      (innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length) := by
    rw [hr.store_eq, hwork]
  have heEq : e = ⟨e.regs, buffers base
      (innerDone w (encodeArray encode target) (encodeArray encode suffix) pending.length)⟩ := by
    exact SubexpScanPrimitives.state_ext rfl hstack
  have hbudget := unaryBudget_le (fun _ => pairCost + 21 * W + 19)
    (pairCost + 21 * W + 19) pending.length (by intros; rfl)
  have hcost : pairCost + 21 * W + 19 + 2 = pairCost + 21 * W + 21 := by omega
  rw [hcost] at hbudget
  refine ⟨n, e.regs, ?_, ?_⟩
  · omega
  · change Eval (innerLoop pair) n ⟨regs, buffers base w⟩ e at he
    rw [heEq] at he
    exact he

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
