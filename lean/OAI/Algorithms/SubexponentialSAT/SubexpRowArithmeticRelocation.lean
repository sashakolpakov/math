import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Source-row arithmetic without overwriting the source caches

Native convolution uses stacks 128--204, while the source caches occupy
128--137. A fixed permutation moves those ten arithmetic slots to 214--223.
Relocation changes no operand widths or numerical parameters and introduces
only the final halt of the installed command.
-/

namespace SubexponentialSAT.SubexpRowArithmeticRelocation

open BitProgram StructuredCalls
open SubexpConvolutionControl (Code Store Data ExecutesIn)

def bankIndex (i : Fin 256) : Fin 256 :=
  if h : 128 ≤ i.val ∧ i.val < 138 then ⟨i.val + 86, by omega⟩
  else if h : 214 ≤ i.val ∧ i.val < 224 then ⟨i.val - 86, by omega⟩
  else i

theorem bankIndex_involutive : Function.Involutive bankIndex := by
  intro i
  by_cases hl : 128 ≤ i.val ∧ i.val < 138
  · have hnl : ¬ (128 ≤ i.val + 86 ∧ i.val + 86 < 138) := by omega
    have hh : 214 ≤ i.val + 86 ∧ i.val + 86 < 224 := by omega
    simp only [bankIndex, dite_eq_left hl, Fin.val_mk, dite_eq_right hnl, dite_eq_left hh]
    apply Fin.ext
    simp
  · by_cases hh : 214 ≤ i.val ∧ i.val < 224
    · have hl' : 128 ≤ i.val - 86 ∧ i.val - 86 < 138 := by omega
      simp only [bankIndex, dite_eq_right hl, dite_eq_left hh, Fin.val_mk, dite_eq_left hl']
      apply Fin.ext
      simp
      omega
    · simp only [bankIndex, dite_eq_right hl, dite_eq_right hh]

def bank : Equiv.Perm (Fin 256) :=
  ⟨bankIndex, bankIndex, bankIndex_involutive, bankIndex_involutive⟩

@[simp] theorem bank_240 : bank 240 = 240 := rfl
@[simp] theorem bank_241 : bank 241 = 241 := rfl
@[simp] theorem bank_242 : bank 242 = 242 := rfl
@[simp] theorem bank_243 : bank 243 = 243 := rfl
@[simp] theorem bank_244 : bank 244 = 244 := rfl
@[simp] theorem bank_245 : bank 245 = 245 := rfl

theorem bank_low (i : Fin 256) (hi : i.val < 128) : bank i = i := by
  have hl : ¬ (128 ≤ i.val ∧ i.val < 138) := by omega
  have hh : ¬ (214 ≤ i.val ∧ i.val < 224) := by omega
  change bankIndex i = i
  simp only [bankIndex, dite_eq_right hl, dite_eq_right hh]

theorem bank_cache (i : Fin 10) :
    bank ⟨128 + i.val, by omega⟩ = ⟨214 + i.val, by omega⟩ := by
  have hl : 128 ≤ 128 + i.val ∧ 128 + i.val < 138 := by omega
  change bankIndex ⟨128 + i.val, by omega⟩ = ⟨214 + i.val, by omega⟩
  apply Fin.ext
  simp only [bankIndex, Fin.val_mk, dite_eq_left hl]
  omega

/-- Install a command at permuted physical stack ports. -/
def relocated (arithmetic : Code) (e : Equiv.Perm (Fin 256)) : Code :=
  .call (ProgramLinking.liftProgram (compiled arithmetic 240 244) id e)

theorem at_run (arithmetic : Code) (e : Equiv.Perm (Fin 256))
    (K : ℕ) (s : Store) (out : List Bool)
    (h : ExecutesIn arithmetic K (s ∘ e) (Function.update (s ∘ e) 244 out)) :
    ExecutesIn (relocated arithmetic e) (K + 1) s (Function.update s (e 244) out) := by
  intro regs
  obtain ⟨n, rf, hn, he⟩ := h regs
  have hself : Function.extend e (s ∘ e) s = s := by
    funext i
    rw [← e.apply_symm_apply i, e.injective.extend_apply]
    simp
  have hin : embedState id e (⟨regs, s⟩ : Data)
      ⟨regs, s ∘ e⟩ = ⟨regs, s⟩ := by
    simp only [embedState, ProgramLinking.extend_id, hself]
  have hout : embedState id e (⟨regs, s⟩ : Data)
      ⟨rf, Function.update (s ∘ e) 244 out⟩ =
      ⟨rf, Function.update s (e 244) out⟩ := by
    simp only [embedState, ProgramLinking.extend_id,
      ProgramLinking.extend_update e.injective, hself]
  have ht := eval_call_lifted (compiled arithmetic 240 244) id e
    (⟨regs, s⟩ : Data) Function.injective_id e.injective (compiled_halt_trace he 240 244)
  exact ⟨n + 1, rf, Nat.add_le_add_right hn 1, by simpa only [relocated, hin, hout] using ht⟩

theorem bank_run (arithmetic : Code) (K : ℕ) (s : Store) (out : List Bool)
    (h : ExecutesIn arithmetic K (s ∘ bank) (Function.update (s ∘ bank) 244 out)) :
    ExecutesIn (relocated arithmetic bank) (K + 1) s (Function.update s 244 out) := by
  simpa only [bank_244] using at_run arithmetic bank K s out h

end SubexponentialSAT.SubexpRowArithmeticRelocation

end OAI.Algorithms
