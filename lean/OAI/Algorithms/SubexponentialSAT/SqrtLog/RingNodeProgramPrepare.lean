import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel

namespace OAI.Algorithms

/-! Constant-control preparation of the padded radix and the final node stream.
The only supplied words are zero padding, binary Q, and unary d. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation BinaryArithmetic SubexpLiftRing

/-- The second successful pop leaves `present = true`, reused for both pushes. -/
abbrev prepareRadix : Cmd 8 15 := .base <|
  .seq (.atom (.pop 5 1 3)) <|
    .seq (.atom (.pop 5 1 3)) <|
      .seq (.atom (.push 5 3)) (.atom (.push 5 3))

theorem prepareRadix_eval (r : Fin 8 → Bool) (tail rank arity out : List Bool) :
    ∃ rf, Eval prepareRadix 4 (data r (false :: false :: tail) rank arity [] [] out)
      (data rf (true :: true :: tail) rank arity [] [] out) := by
  let x0 := data r (false :: false :: tail) rank arity [] [] out
  let x1 := (StructuredProgram.Atom.pop 5 1 3).eval x0
  let x2 := (StructuredProgram.Atom.pop 5 1 3).eval x1
  let x3 := (StructuredProgram.Atom.push 5 3).eval x2
  let x4 := (StructuredProgram.Atom.push 5 3).eval x3
  have he := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 5 1 3) x0)
    (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 5 1 3) x1)
      (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push 5 3) x2)
        (StructuredProgram.Eval.atom (.push 5 3) x3)))
  refine ⟨x4.regs, ?_⟩
  have hx : x4 = data x4.regs (true :: true :: tail) rank arity [] [] out := by
    apply SubexpEnumerationProgram.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [x0, x1, x2, x3, x4, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, execInstr, StructuredProgram.State.ofCfg, data, tapes]
  exact hx ▸ Eval.base he

abbrev preparedCommand : Cmd 8 15 := .seq prepareRadix command

theorem preparedCommand_eval (r : Fin 8 → Bool) (B : ℕ) (hB : 2 ≤ B)
    (rank arity out : List Bool) :
    ∃ n ≤ budget B rank.length arity.length (BinaryArithmetic.toNat rank) + 4, ∃ rf finalRank,
      Eval preparedCommand n (data r (List.replicate B false) rank arity [] [] out)
        (data rf (true :: true :: List.replicate (B-2) false) finalRank arity [] []
          (stream B 3 arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  have hz : List.replicate B false = false :: false :: List.replicate (B-2) false := by
    conv_lhs => rw [show B = (B-2)+2 by omega]
    simp [List.replicate_succ]
  obtain ⟨r1,h1⟩ := prepareRadix_eval r (List.replicate (B-2) false) rank arity out
  rw [← hz] at h1
  have hzv (k : ℕ) : BinaryArithmetic.toNat (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  have hm : BinaryArithmetic.toNat (true :: true :: List.replicate (B-2) false) = 3 := by
    simp [BinaryArithmetic.toNat, bitVal, hzv]
  obtain ⟨n,hn,rf,last,he,hv,hl⟩ := command_eval r1
    (true :: true :: List.replicate (B-2) false) rank arity out (by omega)
  have hw : (true :: true :: List.replicate (B-2) false).length = B := by simp; omega
  rw [hm,hw] at he
  rw [hw] at hn
  exact ⟨4+n,by omega,rf,last,h1.seq he,hv,hl⟩

def preparedProgram := compiled preparedCommand 13 12

/-- Physical generation of the exact reconstruction input ABI from runtime
sizes, including radix construction and every loop/control instruction. -/
theorem preparedProgram_nodes (r : Fin 8 → Bool) (t : ℕ) (ht : 0 < t)
    (rank arity : List Bool) :
    ∃ rf finalRank,
      RunsIn preparedProgram
        (budget (baseWidth 3 t) rank.length arity.length (BinaryArithmetic.toNat rank) + 5)
        ((data r (List.replicate (baseWidth 3 t) false) rank arity [] [] []).withPC
          (some preparedProgram.entry))
        ((data rf (true :: true :: List.replicate (baseWidth 3 t-2) false)
          finalRank arity [] []
          ((List.finRange (BinaryArithmetic.toNat rank)).flatMap
            (fun i => RingProgram.flat (nodeCode t arity.length (i.val+1))))).withPC none) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨n,hn,rf,last,he,hv,hl⟩ := preparedCommand_eval r (baseWidth 3 t)
    (by rw [RingProgram.ternary_baseWidth]; omega) rank arity []
  rw [stream_eq_flat_nodes, List.append_nil] at he
  exact ⟨rf,last,⟨n+1,by omega,compiled_halt_trace he 13 12⟩,hv,hl⟩

/-- Caller-independent relocation: every register and stack outside the fixed
workspace is framed by the checked lifting theorem. -/
theorem preparedProgram_lifted {R S : ℕ} (ρ : Fin 8 → Fin R) (σ : Fin 15 → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (frame : StructuredProgram.State R S) (r : Fin 8 → Bool)
    (t : ℕ) (ht : 0 < t) (rank arity : List Bool) :
    ∃ n ≤ budget (baseWidth 3 t) rank.length arity.length (BinaryArithmetic.toNat rank) + 5,
      ∃ rf finalRank,
      Eval (.call (ProgramLinking.liftProgram preparedProgram ρ σ)) n
        (embedState ρ σ frame
          (data r (List.replicate (baseWidth 3 t) false) rank arity [] [] []))
        (embedState ρ σ frame
          (data rf (true :: true :: List.replicate (baseWidth 3 t-2) false)
            finalRank arity [] []
            ((List.finRange (BinaryArithmetic.toNat rank)).flatMap
              (fun i => RingProgram.flat (nodeCode t arity.length (i.val+1)))))) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨rf,last,⟨n,hn,he⟩,hv,hl⟩ := preparedProgram_nodes r t ht rank arity
  exact ⟨n,hn,rf,last,eval_call_lifted preparedProgram ρ σ frame hρ hσ he,hv,hl⟩

/-- The entire generator has a fixed control table, independent of t,d,Q. -/
theorem preparedProgram_control_size : size preparedCommand + 1 = 182 := rfl

/-- The measured bit-program execution refines to the primitive machine. -/
theorem preparedProgram_primitive (r : Fin 8 → Bool) (t : ℕ) (ht : 0 < t)
    (rank arity : List Bool) :
    ∃ rf finalRank,
      Computation.RunsIn (BitProgram.primitive preparedProgram).step
        (BitProgram.primitiveOverhead preparedProgram *
          (budget (baseWidth 3 t) rank.length arity.length (BinaryArithmetic.toNat rank) + 5))
        (BitProgram.primitiveCfg preparedProgram
          ((data r (List.replicate (baseWidth 3 t) false) rank arity [] [] []).withPC
            (some preparedProgram.entry)))
        (BitProgram.primitiveCfg preparedProgram
          ((data rf (true :: true :: List.replicate (baseWidth 3 t-2) false)
            finalRank arity [] []
            ((List.finRange (BinaryArithmetic.toNat rank)).flatMap
              (fun i => RingProgram.flat (nodeCode t arity.length (i.val+1))))).withPC none)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨rf,last,he,hv,hl⟩ := preparedProgram_nodes r t ht rank arity
  exact ⟨rf,last,BitProgram.primitive_execution preparedProgram he,hv,hl⟩

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
