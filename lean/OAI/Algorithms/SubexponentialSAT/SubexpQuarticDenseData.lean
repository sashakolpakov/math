import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatFrame

namespace OAI.Algorithms

/-! Concrete operand loading for the dense polynomial multiplication caller. -/

namespace SubexponentialSAT.SubexpQuarticDenseCall

open BitProgram StackRoutines StructuredCalls SubexpScanPrimitives
open SubexpQuarticRing SubexpQuarticFlatMul SubexpQuarticFlatLift

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

/-- Empty multiplication workspace with its three persistent parameter caches. -/
def workspace {B : ℕ} (modulus width : List Bool) (t : Quad (Word B)) :
    Stacks (Fin 77) := bankStore (fun _ => []) modulus (flat t) width []

def loadedStacks {B : ℕ} (a b : Quad (Word B)) (stk : Stacks (Fin 128)) :
    Stacks (Fin 128) := Function.update (Function.update stk 11 (flat a)) 12 (flat b)

abbrev loadCmd : Cmd 16 128 :=
  .seq (.call (copyProgram 94 11 24 0 1)) (.call (copyProgram 96 12 24 0 1))

theorem load_eval {B : ℕ} (a b : Quad (Word B))
    (regs : Fin 16 → Bool) (stk : Stacks (Fin 128))
    (ha : stk 94 = flat a) (hb : stk 96 = flat b)
    (h11 : stk 11 = []) (h12 : stk 12 = []) (htmp : stk 24 = []) :
    Eval loadCmd (56 * B + 10) ⟨regs, stk⟩
      ⟨readRegs regs 0 1 none, loadedStacks a b stk⟩ := by
  let d : State 16 128 := ⟨regs, stk⟩
  let d₁ := afterCopy d 94 11 0 1
  have h₁ := copy_eval d 94 11 24 0 1 (by decide) (by decide) (by decide) (by decide) htmp
  have h₂ := copy_eval d₁ 96 12 24 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d₁, d, afterCopy, copyStacks, htmp])
  have hf : afterCopy d₁ 96 12 0 1 =
      (⟨readRegs regs 0 1 none, loadedStacks a b stk⟩ : State 16 128) := by
    apply state_ext
    · simp [d₁, d, afterCopy, readRegs_reset]
    · simp [d₁, d, afterCopy, copyStacks, loadedStacks, ha, hb, h11, h12]
  rw [hf] at h₂
  have total := h₁.seq h₂
  convert total using 1
  all_goals simp [d₁, d, afterCopy, copyStacks, ha, hb, flat_length]
  all_goals omega

theorem loaded_workspace {B : ℕ} (modulus width : List Bool)
    (t a b : Quad (Word B)) (stk : Stacks (Fin 128))
    (h : ∀ i, stk (densePorts i) = workspace modulus width t i) (i : Fin 77) :
    loadedStacks a b stk (densePorts i) = initialStore modulus width t a b i := by
  by_cases h70 : i = 70
  · subst i
    simp [loadedStacks, initialStore, densePorts, densePort]
  · by_cases h71 : i = 71
    · subst i
      simp [loadedStacks, initialStore, densePorts, densePort]
    · have hn11 : densePorts i ≠ (11 : Fin 128) := by
        change densePorts i ≠ densePorts 70
        exact fun he => h70 (densePorts.injective he)
      have hn12 : densePorts i ≠ (12 : Fin 128) := by
        change densePorts i ≠ densePorts 71
        exact fun he => h71 (densePorts.injective he)
      simpa only [loadedStacks, Function.update_of_ne hn12, Function.update_of_ne hn11,
        initialStore, Function.update_of_ne h71, Function.update_of_ne h70, workspace] using h i

theorem result_loaded {B : ℕ} (a b : Quad (Word B)) (result : List Bool)
    (stk : Stacks (Fin 128)) (h11 : stk 11 = []) (h12 : stk 12 = []) :
    resultStacks densePorts result (loadedStacks a b stk) = Function.update stk 13 result := by
  funext j
  by_cases h11j : j = 11
  · subst j
    simp [resultStacks, loadedStacks, densePorts, densePort, h11]
  · by_cases h12j : j = 12
    · subst j
      simp [resultStacks, loadedStacks, densePorts, densePort, h12]
    · by_cases h13j : j = 13
      · subst j
        simp [resultStacks, loadedStacks, densePorts, densePort]
      · simp [resultStacks, loadedStacks, densePorts, densePort, h11j, h12j, h13j]

theorem resultRegs_read (values : Fin 8 → Bool) (regs : Fin 16 → Bool) :
    resultRegs denseRegisters values (readRegs regs 0 1 none) =
      resultRegs denseRegisters values regs := by
  classical
  funext j
  by_cases hj : ∃ i, denseRegisters i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [resultRegs, denseRegisters.injective.extend_apply]
  · have h0 : j ≠ 0 := by
      intro he
      exact hj ⟨0, he.symm⟩
    have h1 : j ≠ 1 := by
      intro he
      exact hj ⟨1, he.symm⟩
    rw [resultRegs_frame _ _ _ _ hj, resultRegs_frame _ _ _ _ hj]
    simp [readRegs, h0, h1]

end SubexponentialSAT.SubexpQuarticDenseCall

end OAI.Algorithms
