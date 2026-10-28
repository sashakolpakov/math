import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmeticSqrt
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmeticQuotient

namespace OAI.Algorithms

/-! Framed runtime square-root and quotient interfaces for parameter pipelines.
All program syntax is fixed by the port maps, never by the operand values. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic


open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

structure SqrtPorts (S : ℕ) where
  input : Fin S
  out : Fin S
  work : Fin 13 ↪ Fin S
  out_ne_input : out ≠ input
  work_ne_input : ∀ i, work i ≠ input
  work_ne_out : ∀ i, work i ≠ out

def SqrtReady {S : ℕ} (p : SqrtPorts S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

@[simp] theorem sqrt_input_ne_work {S : ℕ} (p : SqrtPorts S) (i : Fin 13) :
    p.input ≠ p.work i := (p.work_ne_input i).symm

@[simp] theorem sqrt_out_ne_work {S : ℕ} (p : SqrtPorts S) (i : Fin 13) :
    p.out ≠ p.work i := (p.work_ne_out i).symm

def sqrtStackMap {S : ℕ} (p : SqrtPorts S) : Fin 15 → Fin S :=
  ![p.work 0,p.work 1,p.input,p.work 2,p.work 3,p.work 4,p.work 5,p.work 6,
    p.work 7,p.work 8,p.work 9,p.work 10,p.out,p.work 11,p.work 12]

theorem sqrtStackMap_injective {S : ℕ} (p : SqrtPorts S) :
    Function.Injective (sqrtStackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [sqrtStackMap,p.work.injective.eq_iff,p.work_ne_input,
      p.work_ne_out,p.out_ne_input,Ne.symm p.out_ne_input]

def sqrtBlock {S : ℕ} (p : SqrtPorts S) : Fin 15 ↪ Fin S :=
  ⟨sqrtStackMap p,sqrtStackMap_injective p⟩

abbrev sqrtAt {S : ℕ} (p : SqrtPorts S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram (compiled sqrtLocal 2 12) id (sqrtBlock p))

/-- Only the output word changes. The numeric search range and the actual
padded input length are both present in the source-step bound. -/
theorem sqrtAt_eval {S : ℕ} (p : SqrtPorts S) (d : Data S) (hd : SqrtReady p d) :
    ∃ t rf word,
      Eval (sqrtAt p) t d ⟨rf,Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (d.stacks p.input)) ∧
      word.length ≤ BinaryArithmetic.toNat (d.stacks p.input) ∧
      t ≤ 200001*(BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3 := by
  let a : SqrtData := projectState id (sqrtBlock p) d
  have ha : SqrtLocalReady a := by
    intro i hi
    fin_cases i <;>
      simp_all [a,projectState,sqrtBlock,sqrtStackMap,SqrtReady]
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := sqrtLocal_eval a ha
  have hcall := ArithmeticExpressionSupport.call_on_block sqrtLocal 2 12 (sqrtBlock p)
    d a ⟨rf,Function.update a.stacks 12 word⟩ word he rfl rfl rfl
  have ha2 : a.stacks 2 = d.stacks p.input := rfl
  refine ⟨t+1,rf,word,?_,?_,?_,?_⟩
  · exact hcall
  · simpa only [ha2,CounterPrograms.value_eq_toNat] using hv
  · simpa only [ha2,CounterPrograms.value_eq_toNat] using hl
  · rw [ha2,CounterPrograms.value_eq_toNat] at ht
    have hpos : 0 < (BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3 :=
      Nat.pow_pos (by omega)
    nlinarith

def sqrtProgram {S : ℕ} (p : SqrtPorts S) := compiled (sqrtAt p) p.input p.out

theorem sqrtProgram_runs {S : ℕ} (p : SqrtPorts S) (d : Data S) (hd : SqrtReady p d) :
    ∃ rf word, RunsIn (sqrtProgram p)
      (200002*(BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3)
      (d.withPC (some (sqrtProgram p).entry))
      ((⟨rf,Function.update d.stacks p.out word⟩ : Data S).withPC none) ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (d.stacks p.input)) ∧
      word.length ≤ BinaryArithmetic.toNat (d.stacks p.input) := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := sqrtAt_eval p d hd
  have hpos : 0 < (BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3 :=
    Nat.pow_pos (by omega)
  exact ⟨rf,word,⟨t+1,by nlinarith,compiled_halt_trace he p.input p.out⟩,hv,hl⟩

theorem sqrtProgram_primitive {S : ℕ} (p : SqrtPorts S) (d : Data S) (hd : SqrtReady p d) :
    ∃ rf word, Computation.RunsIn (primitive (sqrtProgram p)).step
      (primitiveOverhead (sqrtProgram p) *
        (200002*(BinaryArithmetic.toNat (d.stacks p.input)+(d.stacks p.input).length+2)^3))
      (primitiveCfg (sqrtProgram p) (d.withPC (some (sqrtProgram p).entry)))
      (primitiveCfg (sqrtProgram p)
        ((⟨rf,Function.update d.stacks p.out word⟩ : Data S).withPC none)) ∧
      BinaryArithmetic.toNat word = Nat.sqrt (BinaryArithmetic.toNat (d.stacks p.input)) ∧
      word.length ≤ BinaryArithmetic.toNat (d.stacks p.input) := by
  obtain ⟨rf,word,hr,hv,hl⟩ := sqrtProgram_runs p d hd
  exact ⟨rf,word,primitive_execution _ hr,hv,hl⟩

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
