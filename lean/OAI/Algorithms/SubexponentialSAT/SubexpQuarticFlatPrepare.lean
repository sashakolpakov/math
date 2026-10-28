import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatData
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Actual preparation and cleanup around the quartic word-bank multiplier. -/

namespace SubexponentialSAT.SubexpQuarticFlatMul

open BitProgram StackRoutines StructuredCalls SubexpScanPrimitives
open SubexpQuarticRing SubexpQuarticMachine FourWordPrograms

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

abbrev splitInputsCmd : Cmd 8 77 :=
  .seq (.call (copyProgram 73 75 69 0 1))
    (.seq (splitCmd splitReductionPorts 0 1)
      (.seq (splitCmd splitLeftPorts 0 1) (splitCmd splitRightPorts 0 1)))

theorem splitInputs_eval {B : ℕ} (t a b : Quad (Word B)) (modulus width : List Bool)
    (hw : width.length = B) (regs : Fin 8 → Bool) :
    Eval splitInputsCmd (196 * B + 137) ⟨regs, initialStore modulus width t a b⟩
      ⟨readRegs regs 0 1 none, bankStore (partialBank t a b) modulus (flat t) width []⟩ := by
  let d : State 8 77 := ⟨regs, initialStore modulus width t a b⟩
  let d₁ := afterCopy d 73 75 0 1
  let d₂ : State 8 77 :=
    ⟨readRegs d₁.regs 0 1 none, splitStacks splitReductionPorts (wordLists t) [] d₁.stacks⟩
  let d₃ : State 8 77 :=
    ⟨readRegs d₂.regs 0 1 none, splitStacks splitLeftPorts (wordLists a) [] d₂.stacks⟩
  have ht := copy_eval d 73 75 69 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d, initialStore, bankStore])
  have h₀ := split_eval splitReductionPorts 0 1 (by decide) (wordLists t) [] width
    d₁.regs d₁.stacks
    (by simp [d₁, d, afterCopy, copyStacks, initialStore, bankStore,
      splitReductionPorts, flat])
    (by simp [d₁, d, afterCopy, copyStacks, initialStore, bankStore, splitReductionPorts])
    (by intro i; simp [hw])
    (by simp [d₁, d, afterCopy, copyStacks, initialStore, bankStore, splitReductionPorts])
    (by simp [d₁, d, afterCopy, copyStacks, initialStore, bankStore, splitReductionPorts])
  have h₁ := split_eval splitLeftPorts 0 1 (by decide) (wordLists a) [] width
    d₂.regs d₂.stacks
    (by simp [d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts, flat])
    (by simp [d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts])
    (by intro i; simp [hw])
    (by simp [d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts])
    (by simp [d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts])
  have h₂ := split_eval splitRightPorts 0 1 (by decide) (wordLists b) [] width
    d₃.regs d₃.stacks
    (by simp [d₃, d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts, splitRightPorts, flat])
    (by simp [d₃, d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts, splitRightPorts])
    (by intro i; simp [hw])
    (by simp [d₃, d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts, splitRightPorts])
    (by simp [d₃, d₂, d₁, d, afterCopy, copyStacks, splitStacks, initialStore,
      bankStore, splitReductionPorts, splitLeftPorts, splitRightPorts])
  have hfinal :
      (⟨readRegs d₃.regs 0 1 none,
        splitStacks splitRightPorts (wordLists b) [] d₃.stacks⟩ : State 8 77) =
      ⟨readRegs regs 0 1 none, bankStore (partialBank t a b) modulus (flat t) width []⟩ := by
    apply state_ext
    · simp [d₃, d₂, d₁, d, afterCopy, readRegs_reset]
    · funext j
      -- Normalize the fixed ports and all saved destination words once,
      -- before splitting into the 77 possible observed stack positions.
      simp only [d₃, d₂, d₁, d, afterCopy, copyStacks, splitStacks]
      dsimp only [splitReductionPorts, splitLeftPorts, splitRightPorts]
      simp [initialStore, bankStore, wordLists, Quad.toFn]
      fin_cases j <;>
        simp [bankStore, partialBank, firstBank, Quad.toFn, Fin.addCases]
  have total := ht.seq (h₀.seq (h₁.seq h₂))
  rw [hfinal] at total
  dsimp [splitInputsCmd]
  convert total using 1 ;
    simp [d, initialStore, bankStore, hw, flat_length] ; omega

def prepareCmd : Cmd 8 77 :=
  .seq splitInputsCmd (BankRoutines.fillCmd 4 69 0 1 tempSlots)

theorem prepare_eval {B : ℕ} (t a b : Quad (Word B)) (modulus width : List Bool)
    (hw : width.length = B) (regs : Fin 8 → Bool) :
    Eval prepareCmd (539 * B + 385) ⟨regs, initialStore modulus width t a b⟩
      ⟨readRegs regs 0 1 none,
        bankStore (fun i => (initialBank t a b i).val) modulus (flat t) width []⟩ := by
  have h₀ := splitInputs_eval t a b modulus width hw regs
  have hempty : ∀ j ∈ tempSlots, bankStore (partialBank t a b) modulus (flat t) width [] j = [] := by
    intro j hj
    rw [tempSlots, List.mem_ofFn] at hj
    obtain ⟨i, rfl⟩ := hj
    simp [partialBank]
  have h₁ := BankRoutines.fill_eval (4 : Fin 77) 69 (0 : Fin 8) 1 tempSlots tempSlots_nodup
    (by norm_num) (by norm_num) (by decide) (by decide)
    (readRegs regs 0 1 none) (bankStore (partialBank t a b) modulus (flat t) width [])
    hempty (by simp [bankStore])
  have hfinal : BankRoutines.fillStacks 4 tempSlots
      (bankStore (partialBank t a b) modulus (flat t) width []) =
      bankStore (fun i => (initialBank t a b i).val) modulus (flat t) width [] := by
    funext j
    fin_cases j <;> simp [BankRoutines.fillStacks, bankStore, initialBank,
      partialBank, firstBank, Quad.toFn, Fin.addCases]
  have hlen : (bankStore (partialBank t a b) modulus (flat t) width [] 4).length = B := by
    simpa [bankStore, partialBank, firstBank, Quad.toFn, Fin.addCases] using a.c0.property
  have total := h₀.seq h₁
  simp only [readRegs_reset, hfinal, hlen, tempSlots_length] at total
  rw [prepareCmd]
  have hcost : (196 * B + 137) + (49 * (7 * B + 5) + 3) = 539 * B + 385 := by
    omega
  rw [← hcost]
  exact total

abbrev finishCmd : Cmd 8 77 :=
  .seq (packCmd packPorts 0 1) (BankRoutines.clearCmd 69 0 1 bankSlots)

theorem output_words {B : ℕ} (bank : Fin 61 → Word B)
    (modulus reduction width : List Bool) :
    bankWords packPorts (bankStore (fun i => (bank i).val) modulus reduction width []) =
      wordLists (mulOutput bank) := by
  funext i
  fin_cases i <;> simp [bankWords, wordPort, packPorts, bankStore, wordLists, mulOutput, Quad.toFn]

theorem finish_eval {B : ℕ} (bank : Fin 61 → Word B)
    (modulus reduction width : List Bool) (regs : Fin 8 → Bool) :
    Eval finishCmd (150 * B + 206)
      ⟨regs, bankStore (fun i => (bank i).val) modulus reduction width []⟩
      ⟨readRegs regs 0 1 none,
        bankStore (fun _ => []) modulus reduction width (flat (mulOutput bank))⟩ := by
  let stk := bankStore (fun i => (bank i).val) modulus reduction width []
  have hp := pack_eval packPorts 0 1 (by decide) regs stk (by simp [stk, packPorts, bankStore])
  have hpacked : packStacks packPorts stk =
      bankStore (fun i => (bank i).val) modulus reduction width (flat (mulOutput bank)) := by
    funext j
    by_cases hj : j = 72
    · subst j
      change flatWords (bankWords packPorts stk) ++ stk 72 = _
      rw [output_words]
      simp [stk, bankStore, flat]
    · simp [packStacks, packPorts, stk, bankStore, hj]
  have hbits : (flatWords (bankWords packPorts stk)).length = 4 * B := by
    rw [output_words]
    exact flat_length (mulOutput bank)
  have hc := BankRoutines.clear_eval_uniform (69 : Fin 77) (0 : Fin 8) 1 bankSlots bankSlots_nodup
    (readRegs regs 0 1 none)
    (bankStore (fun i => (bank i).val) modulus reduction width (flat (mulOutput bank))) B
    (by
      intro j hj
      rw [bankSlots, List.mem_ofFn] at hj
      obtain ⟨i, rfl⟩ := hj
      simp only [bankStore_bank]
      exact (bank i).property)
    (by simp [bankStore])
  have hcleared : BankRoutines.clearBankStacks bankSlots
      (bankStore (fun i => (bank i).val) modulus reduction width (flat (mulOutput bank))) =
      bankStore (fun _ => []) modulus reduction width (flat (mulOutput bank)) := by
    funext j
    by_cases hj : j.val < 61 <;> simp [BankRoutines.clearBankStacks, bankStore, hj]
  rw [hpacked] at hp
  have total := hp.seq hc
  simp only [readRegs_reset, hcleared, bankSlots_length, hbits] at total
  dsimp [finishCmd]
  convert total using 1; omega

theorem prepareCmd_size : size prepareCmd = 607 := by
  simp [prepareCmd, splitInputsCmd, size, splitCmd, takeWord, BankRoutines.size_fillCmd]

theorem finishCmd_size : size finishCmd = 218 := by
  simp [ size, BankRoutines.size_clearCmd]

end SubexponentialSAT.SubexpQuarticFlatMul

end OAI.Algorithms
