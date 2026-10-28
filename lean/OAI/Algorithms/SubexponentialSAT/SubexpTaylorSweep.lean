import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorControl

namespace OAI.Algorithms

/-! Exact finite-control execution of the complete affine coefficient sweep. -/

namespace SubexponentialSAT.SubexpTaylorSweep

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl

variable {C : Type*} (encode : C → List Bool) (B : ℕ)
  (hencode : ∀ a, (encode a).length = B) (hB : 0 < B)
  (base : Words) (hwidth : base.blockWidth.length = B)
  (arithmetic : Cmd 8 87) (step : C → C → C) (K : ℕ)
  (harithmetic : ∀ regs (w : Words) a b,
    w.modulus = base.modulus → w.width = base.width →
    w.reduction = base.reduction → w.point = base.point →
    w.accumulator = encode a → w.coefficient = encode b →
    w.work = [] → w.left = [] → w.right = [] →
    ∃ n ≤ K, ∃ regs', Eval arithmetic n (state regs w)
      (state regs' {w with accumulator := encode (step a b), coefficient := []}))

include hencode hB hwidth harithmetic

theorem tail_eval (xs : List C) (b : C) (packed : List Bool) (regs : Fin 8 → Bool) :
    ∃ n ≤ xs.length * (K + 33 * B + 27) + 6 * B + 3 * packed.length + 7,
      ∃ regs', Eval (SubexpTaylorControl.tail arithmetic) n
        (state (readRegs regs 0 1 (encodeList encode xs).head?)
          (ready encode base xs b packed))
        (state regs' (done base (packed.reverse ++ encodeList encode (sweep step b xs)))) := by
  induction xs generalizing b packed regs with
  | nil =>
      have hloop : Eval (.while 1 (.seq (iteration arithmetic) guard)) 1
          (state (readRegs regs 0 1 none) (ready encode base [] b packed))
          (state (readRegs regs 0 1 none) (ready encode base [] b packed)) :=
        .while_false (by simp [state, readRegs])
      have hfinish := finish_eval (readRegs regs 0 1 none) (ready encode base [] b packed) rfl
      refine ⟨1 + (6 * (encode b).length + 3 * packed.length + 6), ?_,
        readRegs regs 0 1 none, ?_⟩
      · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, hencode]
        omega
      · simpa only [SubexpTaylorControl.tail, ready, done, sweep, encodeList,
          List.flatMap_nil, List.flatMap_cons, List.append_nil, List.head?_nil,
          StackRoutines.readRegs_reset] using hloop.seq hfinish
  | cons a xs ih =>
      obtain ⟨ni, hni, ri, hi⟩ := SubexpTaylorControl.iteration_eval
        encode B hencode base hwidth arithmetic step K harithmetic
        (readRegs regs 0 1 (encodeList encode (a :: xs)).head?) a b xs packed
      have hg := guard_eval ri (ready encode base xs a ((encode (step a b)).reverse ++ packed))
      obtain ⟨nr, hnr, rr, hr⟩ := ih a ((encode (step a b)).reverse ++ packed) ri
      have htest :
          (state (readRegs regs 0 1 (encodeList encode (a :: xs)).head?)
            (ready encode base (a :: xs) b packed)).regs 1 = true := by
        have ha : encode a ≠ [] := by
          intro h
          have := hencode a
          simp [h] at this
          omega
        simp [state, readRegs, encodeList, List.head?_append, ha]
      change Eval (.seq (.while 1 (.seq (iteration arithmetic) guard)) finish) _ _ _ at hr
      cases hr with
      | @seq _ _ nloop nfinish _ middle _ hloop hfinish =>
          have hall := (Eval.while_true htest (hi.seq hg) hloop).seq hfinish
          refine ⟨ni + 1 + nloop + 1 + nfinish, ?_, rr, ?_⟩
          · simp only [List.length_cons, List.length_append, List.length_reverse, hencode] at *
            nlinarith
          · simpa only [SubexpTaylorControl.tail, sweep, encodeList, List.flatMap_cons,
              List.reverse_append, List.reverse_reverse, List.append_assoc] using hall

theorem command_eval (xs : List C) (b : C) (regs : Fin 8 → Bool) :
    ∃ n ≤ xs.length * (K + 33 * B + 27) + 6 * B + 8,
      ∃ regs', Eval (SubexpTaylorControl.command arithmetic) n
        (state regs (ready encode base xs b []))
        (state regs' (done base (encodeList encode (sweep step b xs)))) := by
  have hg := guard_eval regs (ready encode base xs b [])
  obtain ⟨n, hn, rr, hr⟩ := tail_eval encode B hencode hB base hwidth arithmetic step K
    harithmetic xs b [] regs
  refine ⟨1 + n, ?_, rr, ?_⟩
  · simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hn
    omega
  · simpa only [SubexpTaylorControl.command, ready, List.reverse_nil, List.nil_append] using hg.seq hr

end SubexponentialSAT.SubexpTaylorSweep

end OAI.Algorithms
