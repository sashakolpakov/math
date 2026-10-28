import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramRow
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram

namespace OAI.Algorithms

/-! Canonical, positive encodings for exact integer row signatures.  The
added one is common to all assignments and makes the normalizer total on
all legitimate row results, including the empty head. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def canonical (n : ℕ) : List Bool :=
  SubexponentialSAT.SubexpLiftRing.fixedBits (Nat.log2 n+1) n

def normalizeRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def normalizePorts : Fin 3 → Fin 12 := fun i => ⟨i.val+2, by omega⟩

theorem normalizeRegs_injective : Function.Injective normalizeRegs := Fin.castAdd_injective _ _
theorem normalizePorts_injective : Function.Injective normalizePorts := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa [normalizePorts] using this

def normalizeCall : DotCode := .call
  (ProgramLinking.liftProgram SubexponentialSAT.CounterNormalizeProgram.program normalizeRegs normalizePorts)

theorem normalizeCall_eval (regs : Fin 8 → Bool) (W out : List Bool)
    (hp : 0 < SubexponentialSAT.BinaryArithmetic.toNat out) :
    ∃ t ≤ 9*out.length+21, ∃ rf,
      Eval normalizeCall t (dotState regs W [] [] out)
        (dotState rf W [] [] (canonical (SubexponentialSAT.BinaryArithmetic.toNat out))) := by
  have hp' : 0 < SubexponentialSAT.CounterPrograms.value out := by
    simpa only [SubexponentialSAT.CounterPrograms.value_eq_toNat] using hp
  obtain ⟨t, he, ht⟩ := SubexponentialSAT.CounterNormalizeProgram.normalize_eval
    (regs ∘ normalizeRegs) out hp'
  have ha : projectState normalizeRegs normalizePorts (dotState regs W [] [] out) =
      SubexponentialSAT.CounterNormalizeProgram.state (regs ∘ normalizeRegs) out [] := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ normalizeRegs))
    funext i; fin_cases i <;> rfl
  rw [←ha] at he
  have h := eval_call_from_state SubexponentialSAT.CounterNormalizeProgram.program normalizeRegs normalizePorts
    (dotState regs W [] [] out) normalizeRegs_injective normalizePorts_injective
    (compiled_halt_trace he 0 0)
  let rf := (embedState normalizeRegs normalizePorts (dotState regs W [] [] out)
    (SubexponentialSAT.CounterNormalizeProgram.state SubexponentialSAT.CounterNormalizeProgram.zeroRegs
      (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) [])).regs
  have hend : embedState normalizeRegs normalizePorts (dotState regs W [] [] out)
      (SubexponentialSAT.CounterNormalizeProgram.state SubexponentialSAT.CounterNormalizeProgram.zeroRegs
        (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) []) =
      dotState rf W [] [] (canonical (SubexponentialSAT.BinaryArithmetic.toNat out)) := by
    apply embedState_eq_of_ports normalizeRegs normalizePorts _ _ _
      normalizeRegs_injective normalizePorts_injective
    · intro i
      exact (embedState_register normalizeRegs normalizePorts _ _ normalizeRegs_injective i)
    · intro i hi
      exact (embedState_register_frame normalizeRegs normalizePorts _ _ i hi)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0, h.symm⟩
      fin_cases i <;> simp_all [dotState]
  simp only [SubexponentialSAT.CounterPrograms.value_eq_toNat] at h
  change Eval normalizeCall (t+1) _
    (embedState normalizeRegs normalizePorts _
      (SubexponentialSAT.CounterNormalizeProgram.state _ (canonical _) [])) at h
  rw [hend] at h
  exact ⟨t+1, by omega, rf, h⟩

def canonicalRowCommand : DotCode := .seq rowCommand normalizeCall
def canonicalRowProgram := compiled canonicalRowCommand 9 2

def canonicalRowBudget (W : List Bool) (coeffs : List (List Bool)) : ℕ :=
  rowBudget W coeffs [true] + 9*rowWidth W coeffs [true]+22

theorem canonicalRowCommand_eval (regs : Fin 8 → Bool) (W : List Bool)
    (coeffs : List (List Bool)) (bits : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ t ≤ canonicalRowBudget W coeffs, ∃ rf,
      Eval canonicalRowCommand t (dotState regs W coeffs bits [true])
        (dotState rf W [] [] (canonical (1+rowValue W coeffs bits))) := by
  obtain ⟨t,ht,rm,out,he,hv,hl⟩ := rowCommand_eval regs W coeffs bits [true] hlen
  have hv' : SubexponentialSAT.BinaryArithmetic.toNat out = 1+rowValue W coeffs bits := by
    simpa [SubexponentialSAT.BinaryArithmetic.toNat] using hv
  obtain ⟨u,hu,rf,hf⟩ := normalizeCall_eval rm W out (by omega)
  rw [hv'] at hf
  exact ⟨t+u, by dsimp [canonicalRowBudget]; omega, rf, he.seq hf⟩

theorem canonicalRow_runsIn (regs : Fin 8 → Bool) (W : List Bool)
    (coeffs : List (List Bool)) (bits : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ rf, RunsIn canonicalRowProgram (canonicalRowBudget W coeffs+1)
      ((dotState regs W coeffs bits [true]).withPC (some canonicalRowProgram.entry))
      ((dotState rf W [] [] (canonical (1+rowValue W coeffs bits))).withPC none) := by
  obtain ⟨t,ht,rf,he⟩ := canonicalRowCommand_eval regs W coeffs bits hlen
  exact ⟨rf,⟨t+1,by omega,compiled_halt_trace he 9 2⟩⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
