import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpInverseProgram
import OAI.Algorithms.SubexponentialSAT.SubexpConstantPrograms
import OAI.Algorithms.SubexponentialSAT.FourWordPrograms
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Physical marshalling for the geometric inverse bank. All persistent
inputs are flat words. The scalar zero and every working bank word are
constructed by actual finite programs. -/

namespace SubexponentialSAT.SubexpQuarticFlatInverse

open BitProgram StructuredCalls SubexpScanPrimitives StackRoutines FourWordPrograms
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 8 96
abbrev Code := Cmd 8 96
abbrev Store := Fin 96 → List Bool
abbrev Bank (B : ℕ) := Fin 71 → Word B

def afterClear (d : Data) (src : Fin 96) (v p : Fin 8) : Data :=
  ⟨readRegs d.regs v p none, clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 96) (v p : Fin 8) (d : Data) :
    Eval (.call (clearProgram src v p)) (2 * (d.stacks src).length + 3) d (afterClear d src v p) :=
  BankRoutines.clear_call_eval src v p d.regs d.stacks

structure Inputs where
  modulus : List Bool
  a : List Bool
  seed : List Bool
  reduction : List Bool
  unit : List Bool
  minusOne : List Bool
  width : List Bool
  counter : List Bool

def words {B : ℕ} (q : Quad (Word B)) : Words := fun i => (q.toFn i).val
def flat {B : ℕ} (q : Quad (Word B)) : List Bool := flatWords (words q)

@[simp] theorem words_length {B : ℕ} (q : Quad (Word B)) (i : Fin 4) :
    (words q i).length = B := (q.toFn i).property

@[simp] theorem flat_length {B : ℕ} (q : Quad (Word B)) : (flat q).length = 4 * B := by
  simp [flat, flatWords]
  omega

theorem flat_eq_encode {B : ℕ} (q : Quad (Word B)) : flat q = SubexpFlatAdd.encode q := by
  simp [flat, flatWords, words, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

def inputs {B : ℕ} (modulus width counter : List Bool)
    (t a b unit : Quad (Word B)) (minusOne : Word B) : Inputs :=
  ⟨modulus, flat a, flat b, flat t, flat unit, minusOne.val, width, counter⟩

def store (I : Inputs) (bank : Fin 71 → List Bool) (count result : List Bool) : Store :=
  fun i => if h : i.val < 71 then bank ⟨i.val, h⟩
    else if i = 76 then I.modulus
    else if i = 80 then count
    else if i = 82 then I.a
    else if i = 83 then I.seed
    else if i = 84 then I.reduction
    else if i = 85 then I.unit
    else if i = 86 then I.minusOne
    else if i = 87 then I.width
    else if i = 88 then I.counter
    else if i = 89 then result else []

def emptyStore (I : Inputs) (result : List Bool) : Store := store I (fun _ => []) [] result
def typedStore {B : ℕ} (I : Inputs) (bank : Bank B) (count result : List Bool) : Store :=
  store I (fun i => (bank i).val) count result

def bankPort (i : Fin 71) : Fin 96 := Fin.castAdd 25 i
def blockStart : Fin 4 → ℕ := ![0, 4, 8, 65]
def blockPort (j i : Fin 4) : Fin 71 := ⟨blockStart j + i.val, by fin_cases j <;> simp [blockStart] <;> omega⟩
def sourcePort : Fin 4 → Fin 96 := ![84, 82, 83, 85]
def blockPorts (j : Fin 4) : List (Fin 96) :=
  [bankPort (blockPort j 0), bankPort (blockPort j 1),
    bankPort (blockPort j 2), bankPort (blockPort j 3)]

def splitPorts (j : Fin 4) : Fin 8 ↪ Fin 96 :=
  ⟨![90, 87, 91, 92, bankPort (blockPort j 0), bankPort (blockPort j 1),
      bankPort (blockPort j 2), bankPort (blockPort j 3)], by fin_cases j <;> decide⟩

@[simp] theorem splitPorts_zero (j : Fin 4) : splitPorts j 0 = 90 := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_one (j : Fin 4) : splitPorts j 1 = 87 := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_two (j : Fin 4) : splitPorts j 2 = 91 := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_three (j : Fin 4) : splitPorts j 3 = 92 := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_four (j : Fin 4) :
    splitPorts j 4 = bankPort (blockPort j 0) := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_five (j : Fin 4) :
    splitPorts j 5 = bankPort (blockPort j 1) := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_six (j : Fin 4) :
    splitPorts j 6 = bankPort (blockPort j 2) := by
  fin_cases j <;> decide

@[simp] theorem splitPorts_seven (j : Fin 4) :
    splitPorts j 7 = bankPort (blockPort j 3) := by
  fin_cases j <;> decide

def packPorts : Fin 8 ↪ Fin 96 := ⟨![89, 87, 91, 92, 57, 58, 59, 60], by decide⟩
def zeroPorts : Fin 3 ↪ Fin 96 := ⟨![70, 93, 94], by decide⟩
def native : Fin 82 ↪ Fin 96 := ⟨Fin.castAdd 14, Fin.castAdd_injective 82 14⟩

def fillPorts : List (Fin 96) := (List.finRange 70).map (Fin.castAdd 26)
def clearPorts : List (Fin 96) := (List.finRange 71).map bankPort

@[simp] theorem mem_fillPorts (i : Fin 96) : i ∈ fillPorts ↔ i.val < 70 := by
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
    exact j.isLt
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val, h⟩, by simp, Fin.ext rfl⟩

@[simp] theorem mem_clearPorts (i : Fin 96) : i ∈ clearPorts ↔ i.val < 71 := by
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
    exact j.isLt
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val, h⟩, by simp, Fin.ext rfl⟩

def zeroWord (B : ℕ) : Word B := ⟨fixedBits B 0, fixedBits_length B 0⟩
def putQuad {B : ℕ} (bank : Bank B) (j : Fin 4) (q : Quad (Word B)) : Bank B :=
  Function.update (Function.update (Function.update (Function.update bank
    (blockPort j 0) q.c0) (blockPort j 1) q.c1) (blockPort j 2) q.c2) (blockPort j 3) q.c3

def initialBank {B : ℕ} (t a b unit : Quad (Word B)) (minusOne : Word B) : Bank B :=
  Function.update (putQuad (putQuad (putQuad (putQuad (fun _ => zeroWord B)
    0 t) 1 a) 2 b) 3 unit) 69 minusOne

def zeroCall : Code := .call (ProgramLinking.liftProgram (SubexpConstantPrograms.program false) id zeroPorts)
def initializeZero : Code := .seq (.call (copyProgram 87 70 92 0 1))
  (.seq zeroCall (BankRoutines.fillCmd 70 92 0 1 fillPorts))
def replaceQuad (j : Fin 4) : Code :=
  .seq (BankRoutines.clearCmd 92 0 1 (blockPorts j))
    (.seq (.call (copyProgram (sourcePort j) 90 92 0 1)) (splitCmd (splitPorts j) 0 1))
def replaceMinus : Code := .seq (.call (clearProgram 69 0 1)) (.call (copyProgram 86 69 92 0 1))
def prepare : Code := .seq initializeZero (.seq (replaceQuad 0)
  (.seq (replaceQuad 1) (.seq (replaceQuad 2) (.seq (replaceQuad 3)
    (.seq replaceMinus (.call (copyProgram 88 80 92 0 1)))))))
def finish : Code := .seq (packCmd packPorts 0 1)
  (.seq (BankRoutines.clearCmd 92 0 1 clearPorts) (.call (clearProgram 80 0 1)))

@[simp] theorem store_bank (I : Inputs) (bank : Fin 71 → List Bool) (count result : List Bool)
    (i : Fin 71) : store I bank count result (bankPort i) = bank i := by
  simp [store, bankPort]

theorem bank_values_update {B : ℕ} (bank : Bank B) (i : Fin 71) (w : Word B) :
    (fun j => (Function.update bank i w j).val) = Function.update (fun j => (bank j).val) i w.val := by
  funext j
  by_cases h : j = i <;> simp [h]

theorem store_update (I : Inputs) (bank : Fin 71 → List Bool) (count result : List Bool)
    (j : Fin 71) (w : List Bool) :
    store I (Function.update bank j w) count result =
      Function.update (store I bank count result) (bankPort j) w := by
  funext i
  by_cases he : i = bankPort j
  · subst i; simp
  · by_cases hi : i.val < 71
    · have hj : (⟨i.val, hi⟩ : Fin 71) ≠ j := by
        intro h
        apply he
        apply Fin.ext
        exact congrArg (fun x : Fin 71 => x.val) h
      simp [store, hi, he, hj]
    · simp [store, hi, he]

theorem typedStore_update {B : ℕ} (I : Inputs) (bank : Bank B) (count result : List Bool)
    (j : Fin 71) (w : Word B) :
    typedStore I (Function.update bank j w) count result =
      Function.update (typedStore I bank count result) (bankPort j) w.val := by
  simp only [typedStore, bank_values_update, store_update]

theorem zeroCall_eval (d : Data) (h93 : d.stacks 93 = []) (h94 : d.stacks 94 = []) :
    ∃ rf, Eval zeroCall (7 * (d.stacks 70).length + 7) d
      ⟨rf, Function.update d.stacks 70 (fixedBits (d.stacks 70).length 0)⟩ := by
  obtain ⟨rf, ht⟩ := SubexpConstantPrograms.run_literal false d.regs (d.stacks 70) (by simp)
  have hi : projectState id zeroPorts d = SubexpConstantPrograms.state d.regs (d.stacks 70) [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [zeroPorts, ModularPrograms.operandStacks, h93, h94]
  have he := eval_call_from_state (SubexpConstantPrograms.program false) id zeroPorts d
    Function.injective_id zeroPorts.injective (by simpa [hi] using ht)
  have ho : embedState id zeroPorts d
      (SubexpConstantPrograms.state rf (fixedBits (d.stacks 70).length 0) []) =
      (⟨rf, Function.update d.stacks 70 (fixedBits (d.stacks 70).length 0)⟩ : Data) := by
    apply embedState_eq id zeroPorts Function.injective_id zeroPorts.injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [zeroPorts, SubexpConstantPrograms.state,
        ModularPrograms.operandStacks, h93, h94]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i hi
      have h70 : i ≠ 70 := fun h => hi ⟨0, by simpa [zeroPorts] using h.symm⟩
      simp [h70]
  refine ⟨rf, ?_⟩
  simpa [zeroCall, ho] using he

theorem initializeZero_eval (I : Inputs) (B : ℕ) (hw : I.width.length = B) (regs : Fin 8 → Bool) :
    ∃ rf, Eval initializeZero (504 * B + 365) ⟨regs, emptyStore I []⟩
      ⟨rf, typedStore I (fun _ => zeroWord B) [] []⟩ := by
  let d : Data := ⟨regs, emptyStore I []⟩
  let a := afterCopy d 87 70 0 1
  have hc := copy_eval d 87 70 92 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d, emptyStore, store])
  obtain ⟨rf, hz⟩ := zeroCall_eval a
    (by simp [a, d, afterCopy, copyStacks, emptyStore, store])
    (by simp [a, d, afterCopy, copyStacks, emptyStore, store])
  have halen : (a.stacks 70).length = B := by
    simp [a, d, afterCopy, copyStacks, emptyStore, store, hw]
  rw [halen] at hz
  let s := Function.update a.stacks 70 (fixedBits B 0)
  have hfill := BankRoutines.fill_eval (70 : Fin 96) 92 (0 : Fin 8) 1 fillPorts
    (by decide) (by decide) (by decide) (by decide) (by decide) rf s
    (by
      intro i hi
      have hi70 := (mem_fillPorts i).mp hi
      have hi71 : i.val < 71 := by omega
      have hne : i ≠ 70 := by intro h; subst i; norm_num at hi70
      simp [s, a, d, afterCopy, copyStacks, emptyStore, store, hi71, hne])
    (by simp [s, a, d, afterCopy, copyStacks, emptyStore, store])
  have hout : BankRoutines.fillStacks 70 fillPorts s = typedStore I (fun _ => zeroWord B) [] [] := by
    funext i
    fin_cases i <;> simp [BankRoutines.fillStacks, s, a, d, afterCopy,
      copyStacks, emptyStore, typedStore, store, zeroWord]
  have hall := hc.seq (hz.seq hfill)
  refine ⟨readRegs rf 0 1 none, ?_⟩
  rw [hout] at hall
  convert hall using 1 <;>
    simp [initializeZero, a, d, afterCopy, copyStacks, emptyStore, store, hw, s, fillPorts]
  ring

theorem replaceQuad_eval {B : ℕ} (I : Inputs) (bank : Bank B) (j : Fin 4)
    (q : Quad (Word B)) (hq : store I (fun k => (bank k).val) [] [] (sourcePort j) = flat q)
    (hw : I.width.length = B) (regs : Fin 8 → Bool) :
    Eval (replaceQuad j) (92 * B + 64) ⟨regs, typedStore I bank [] []⟩
      ⟨readRegs regs 0 1 none, typedStore I (putQuad bank j q) [] []⟩ := by
  let d : Data := ⟨regs, typedStore I bank [] []⟩
  let a : Data := ⟨readRegs regs 0 1 none, BankRoutines.clearBankStacks (blockPorts j) d.stacks⟩
  let b := afterCopy a (sourcePort j) 90 0 1
  have hc := BankRoutines.clear_eval_uniform (92 : Fin 96) (0 : Fin 8) 1 (blockPorts j)
    (by fin_cases j <;> decide) regs d.stacks B
    (by
      intro i hi
      simp only [blockPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;>
        simpa [d, typedStore] using (bank _).property)
    (by simp [d, typedStore, store])
  have hcopy := copy_eval a (sourcePort j) 90 92 0 1
    (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by decide) (by decide)
    (by fin_cases j <;> simp [a, d, BankRoutines.clearBankStacks, blockPorts, blockPort,
      blockStart, bankPort, typedStore, store])
  have hasource : a.stacks (sourcePort j) = flat q := by
    convert hq using 1
    fin_cases j <;> simp [a, d, BankRoutines.clearBankStacks, blockPorts, blockPort,
      blockStart, bankPort, sourcePort, typedStore]
  have hsplit := split_eval (splitPorts j) (0 : Fin 8) 1 (by decide)
    (words q) [] I.width b.regs b.stacks
    (by fin_cases j <;> simpa [b, afterCopy, copyStacks, splitPorts, flat, a, d,
      BankRoutines.clearBankStacks, typedStore, store, blockPorts, bankPort, blockPort,
      blockStart, sourcePort] using hasource)
    (by fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitPorts,
      BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
      typedStore, store])
    (by intro i; simp [hw])
    (by fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitPorts,
      BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
      typedStore, store])
    (by fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitPorts,
      BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
      typedStore, store])
  have hout : splitStacks (splitPorts j) (words q) [] b.stacks = typedStore I (putQuad bank j q) [] [] := by
    simp only [putQuad, typedStore_update]
    funext i
    by_cases hi90 : i = 90
    · subst i
      fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitStacks,
        BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
        typedStore, store, words, Quad.toFn]
    by_cases h0 : i = bankPort (blockPort j 0)
    · subst i
      fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitStacks,
        BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
        typedStore, store, words, Quad.toFn]
    by_cases h1 : i = bankPort (blockPort j 1)
    · subst i
      fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitStacks,
        BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
        typedStore, store, words, Quad.toFn]
    by_cases h2 : i = bankPort (blockPort j 2)
    · subst i
      fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitStacks,
        BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
        typedStore, store, words, Quad.toFn]
    by_cases h3 : i = bankPort (blockPort j 3)
    · subst i
      fin_cases j <;> simp [b, a, d, afterCopy, copyStacks, splitStacks,
        BankRoutines.clearBankStacks, blockPorts, blockPort, blockStart, bankPort, sourcePort,
        typedStore, store, words, Quad.toFn, Function.update_apply]
    simp [b, a, d, afterCopy, copyStacks, splitStacks, splitPorts,
      BankRoutines.clearBankStacks, blockPorts, Function.update_apply, hi90, h0, h1, h2, h3]
  rw [hout] at hsplit
  rw [hasource, flat_length] at hcopy
  rw [hw] at hsplit
  have hregs : readRegs b.regs 0 1 none = readRegs regs 0 1 none := by
    simp [b, a, afterCopy, readRegs_reset]
  rw [hregs] at hsplit
  have hall := hc.seq (hcopy.seq hsplit)
  convert hall using 1 <;> simp [replaceQuad, blockPorts]
  ring

theorem replaceMinus_eval {B : ℕ} (I : Inputs) (bank : Bank B) (minusOne : Word B)
    (hm : I.minusOne = minusOne.val) (regs : Fin 8 → Bool) :
    Eval replaceMinus (9 * B + 8) ⟨regs, typedStore I bank [] []⟩
      ⟨readRegs regs 0 1 none, typedStore I (Function.update bank 69 minusOne) [] []⟩ := by
  let d : Data := ⟨regs, typedStore I bank [] []⟩
  let a := afterClear d 69 0 1
  have hc := clear_eval 69 0 1 d
  have hp := copy_eval a 86 69 92 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [a, d, afterClear, clearStacks, typedStore, store])
  have hout : copyStacks 86 69 a.stacks = typedStore I (Function.update bank 69 minusOne) [] [] := by
    rw [typedStore_update]
    funext i
    by_cases hi : i = 69 <;>
      simp [a, d, afterClear, clearStacks, copyStacks, hi, typedStore, store, hm, bankPort]
  have hall := hc.seq hp
  dsimp only [afterCopy] at hall
  rw [hout] at hall
  convert hall using 1 <;>
    simp [replaceMinus, a, d, afterClear, clearStacks, typedStore, store, hm,
      (bank 69).property, minusOne.property, readRegs_reset]
  ring

theorem prepare_eval {B : ℕ} (modulus width counter : List Bool)
    (t a b unit : Quad (Word B)) (minusOne : Word B) (hw : width.length = B) (regs : Fin 8 → Bool) :
    ∃ rf, Eval prepare (881 * B + 7 * counter.length + 634)
      ⟨regs, emptyStore (inputs modulus width counter t a b unit minusOne) []⟩
      ⟨rf, typedStore (inputs modulus width counter t a b unit minusOne)
        (initialBank t a b unit minusOne) counter []⟩ := by
  let I := inputs modulus width counter t a b unit minusOne
  let bank₀ : Bank B := fun _ => zeroWord B
  let bank₁ := putQuad bank₀ 0 t
  let bank₂ := putQuad bank₁ 1 a
  let bank₃ := putQuad bank₂ 2 b
  let bank₄ := putQuad bank₃ 3 unit
  obtain ⟨rf, hz⟩ := initializeZero_eval I B hw regs
  have h0 := replaceQuad_eval I bank₀ 0 t rfl hw rf
  have h1 := replaceQuad_eval I bank₁ 1 a rfl hw (readRegs rf 0 1 none)
  have h2 := replaceQuad_eval I bank₂ 2 b rfl hw (readRegs rf 0 1 none)
  have h3 := replaceQuad_eval I bank₃ 3 unit rfl hw (readRegs rf 0 1 none)
  have hm := replaceMinus_eval I bank₄ minusOne rfl (readRegs rf 0 1 none)
  let d : Data := ⟨readRegs rf 0 1 none, typedStore I (initialBank t a b unit minusOne) [] []⟩
  have hc := copy_eval d 88 80 92 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d, typedStore, store])
  have hout : copyStacks 88 80 d.stacks = typedStore I (initialBank t a b unit minusOne) counter [] := by
    funext i
    by_cases hi : i = 80
    · subst i; simp [d, copyStacks, typedStore, store, I, inputs]
    · simp [d, copyStacks, typedStore, store, I, inputs, hi]
  dsimp only [afterCopy] at hc
  rw [hout] at hc
  have hd88 : d.stacks 88 = counter := rfl
  have hregs : readRegs d.regs 0 1 none = readRegs rf 0 1 none := by
    simp [d, readRegs_reset]
  rw [hd88, hregs] at hc
  simp only [readRegs_reset] at h1 h2 h3 hm hc
  have hall := hz.seq (h0.seq (h1.seq (h2.seq (h3.seq (hm.seq hc)))))
  refine ⟨readRegs rf 0 1 none, ?_⟩
  convert hall using 1
  all_goals first | rfl | ring

def output {B : ℕ} (bank : Bank B) : Quad (Word B) := SubexpInverseProgram.output bank

theorem finish_eval {B : ℕ} (I : Inputs) (bank : Bank B) (count : List Bool) (regs : Fin 8 → Bool) :
    Eval finish (170 * B + 2 * count.length + 239) ⟨regs, typedStore I bank count []⟩
      ⟨readRegs regs 0 1 none, emptyStore I (flat (output bank))⟩ := by
  let d : Data := ⟨regs, typedStore I bank count []⟩
  have hp := pack_eval packPorts (0 : Fin 8) 1 (by decide) regs d.stacks
    (by simp [d, typedStore, store, packPorts])
  have hwords : bankWords packPorts d.stacks = words (output bank) := by
    funext i
    fin_cases i <;> simp [d, packPorts, bankWords, wordPort, typedStore, store, words,
      output, SubexpInverseProgram.output, SubexpInverseProgram.lowerBank,
      SubexpQuarticMachine.mulOutput, Quad.toFn]
  have hpack : packStacks packPorts d.stacks = typedStore I bank count (flat (output bank)) := by
    unfold packStacks
    rw [hwords]
    change Function.update d.stacks 89 (flat (output bank) ++ d.stacks 89) = _
    funext i
    by_cases hi : i = 89
    · subst i; simp [d, typedStore, store]
    · simp [d, typedStore, store, hi]
  rw [hwords, hpack] at hp
  change Eval (packCmd packPorts 0 1) (7 * (flat (output bank)).length + 20) _ _ at hp
  rw [flat_length] at hp
  let a := typedStore I bank count (flat (output bank))
  have hc := BankRoutines.clear_eval_uniform (92 : Fin 96) (0 : Fin 8) 1 clearPorts
    (by decide) (readRegs regs 0 1 none) a B
    (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      simpa [a, typedStore] using (bank j).property)
    (by simp [a, typedStore, store])
  have hclear : BankRoutines.clearBankStacks clearPorts a = store I (fun _ => []) count (flat (output bank)) := by
    funext i
    by_cases hi : i.val < 71 <;> simp [BankRoutines.clearBankStacks, a, typedStore, store, hi]
  rw [hclear] at hc
  have hclearlen : clearPorts.length = 71 := by simp [clearPorts]
  rw [hclearlen] at hc
  let e : Data := ⟨readRegs regs 0 1 none, store I (fun _ => []) count (flat (output bank))⟩
  have hf := clear_eval 80 0 1 e
  have hend : clearStacks 80 e.stacks = emptyStore I (flat (output bank)) := by
    funext i
    by_cases hi : i = 80
    · subst i; simp [e, clearStacks, emptyStore, store]
    · simp [e, clearStacks, emptyStore, store, hi]
  dsimp only [afterClear] at hf
  rw [hend] at hf
  have he80 : e.stacks 80 = count := rfl
  have hregs : readRegs e.regs 0 1 none = readRegs regs 0 1 none := by
    simp [e, readRegs_reset]
  rw [he80, hregs] at hf
  simp only [readRegs_reset] at hc hf
  have hall := hp.seq (hc.seq hf)
  convert hall using 1
  all_goals first | rfl | ring

end SubexponentialSAT.SubexpQuarticFlatInverse

end OAI.Algorithms
