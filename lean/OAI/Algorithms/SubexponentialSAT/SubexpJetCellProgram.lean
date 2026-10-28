import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 128
abbrev Code := Cmd 16 128

def arrayPorts : Fin 8 → Fin 128 := ![102, 112, 113, 104, 114, 115, 116, 117]

theorem arrayPorts_injective : Function.Injective arrayPorts := by
  decide

def copyIndex : Code := .call (StackRoutines.copyProgram 103 113 114 0 1)

def arrayRead : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.readProgram (0 : Fin 16) 1) id arrayPorts)

def arrayReplace : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.replaceProgram (0 : Fin 16) 1) id arrayPorts)

def moveForward (src dst : Fin 128) : Code :=
  .seq (.call (StackRoutines.transferProgram src 118 0 1))
    (.call (StackRoutines.transferProgram 118 dst 0 1))

def clear (src : Fin 128) : Code := .call (StackRoutines.clearProgram src 0 1)

def readOut (d : Data) (record : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 113 []) 112 (record ++ d.stacks 112)⟩

def replaceOut (d : Data) (earlier : List (List Bool)) (replacement rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 113 []) 102
      (earlier.flatten ++ (replacement ++ rest))⟩

def moveOut (d : Data) (src dst : Fin 128) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src ++ d.stacks dst)⟩

def clearOut (d : Data) (src : Fin 128) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem copyIndex_eval (d : Data) (htmp : d.stacks 114 = []) :
    Eval copyIndex (7 * (d.stacks 103).length + 5) d (afterCopy d 103 113 0 1) :=
  copy_eval d 103 113 114 0 1 (by decide) (by decide) (by decide) (by decide) htmp

theorem moveForward_eval (d : Data) (src dst : Fin 128)
    (hsd : src ≠ dst) (hst : src ≠ 118) (hdt : dst ≠ 118)
    (htmp : d.stacks 118 = []) :
    Eval (moveForward src dst) (6 * (d.stacks src).length + 6) d (moveOut d src dst) := by
  have h₁ := transfer_eval d src 118 0 1 hst (by decide)
  have h₂ := transfer_eval (afterTransfer d src 118 0 1) 118 dst 0 1 hdt.symm (by decide)
  have hout : afterTransfer (afterTransfer d src 118 0 1) 118 dst 0 1 =
      moveOut d src dst := by
    apply state_ext
    · simp [afterTransfer, moveOut, StackRoutines.readRegs_reset]
    · funext j
      by_cases hd : j = dst
      · subst j
        simp [afterTransfer, moveOut, StackRoutines.transferStacks, htmp,
          hsd.symm, hdt ]
      · by_cases ht : j = 118
        · subst j
          simp [afterTransfer, moveOut, StackRoutines.transferStacks, htmp,
            hd, hst.symm]
        · simp [afterTransfer, moveOut, StackRoutines.transferStacks, hd, ht]
  have hlen : ((afterTransfer d src 118 0 1).stacks 118).length = (d.stacks src).length := by
    simp [afterTransfer, StackRoutines.transferStacks, htmp]
  simpa only [moveForward, hout, hlen, show ∀ n : ℕ, (3*n+3)+(3*n+3)=6*n+6 by omega]
    using Eval.seq h₁ h₂

theorem clear_eval (d : Data) (src : Fin 128) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (clearOut d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clearOut, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

private theorem embed_array_input (d : Data) :
    embedState id arrayPorts d ⟨d.regs, d.stacks ∘ arrayPorts⟩ = d := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

private theorem embed_array_read (d : Data) (record : List Bool) :
    embedState id arrayPorts d
      ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record (d.stacks ∘ arrayPorts)⟩ =
        readOut d record := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intro i
    fin_cases i <;> simp [readOut, arrayPorts, ArrayUpdatePrograms.readStacks]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h₁ : j ≠ 112 := fun h => hj ⟨1, by simpa [arrayPorts] using h.symm⟩
    have h₂ : j ≠ 113 := fun h => hj ⟨2, by simpa [arrayPorts] using h.symm⟩
    simp [readOut, h₁, h₂]

private theorem embed_array_replace (d : Data) (earlier : List (List Bool))
    (replacement rest : List Bool) :
    embedState id arrayPorts d
      ⟨readRegs d.regs 0 1 none,
        ArrayUpdatePrograms.replaceStacks earlier replacement rest (d.stacks ∘ arrayPorts)⟩ =
          replaceOut d earlier replacement rest := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intro i
    fin_cases i <;> simp [replaceOut, arrayPorts, ArrayUpdatePrograms.replaceStacks]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h₁ : j ≠ 102 := fun h => hj ⟨0, by simpa [arrayPorts] using h.symm⟩
    have h₂ : j ≠ 113 := fun h => hj ⟨2, by simpa [arrayPorts] using h.symm⟩
    simp [replaceOut, h₁, h₂]

theorem arrayRead_eval (d : Data) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (record ++ rest))
    (hw : d.stacks 104 = widthWord) (hi : d.stacks 113 = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) :
    Eval arrayRead
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      d (readOut d record) := by
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 16) 1 (by decide)
    earlier record rest widthWord indexWord d.regs (d.stacks ∘ arrayPorts)
    hs hw hi hiLen hrows hlen h114 h115 h116 h117
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 16) 1)
    id arrayPorts d Function.injective_id arrayPorts_injective
    (a := ⟨d.regs, d.stacks ∘ arrayPorts⟩)
    (b := ⟨readRegs d.regs 0 1 none,
      ArrayUpdatePrograms.readStacks record (d.stacks ∘ arrayPorts)⟩) ht
  simpa only [arrayRead, embed_array_input, embed_array_read] using he

theorem arrayReplace_eval (d : Data) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (record ++ rest))
    (hn : d.stacks 112 = replacement)
    (hw : d.stacks 104 = widthWord) (hi : d.stacks 113 = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) :
    Eval arrayReplace
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      d (replaceOut d earlier replacement rest) := by
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 16) 1 (by decide)
    earlier record replacement rest widthWord indexWord d.regs (d.stacks ∘ arrayPorts)
    hs hn hw hi hiLen hrows hlen hnew h114 h115 h116 h117
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 16) 1)
    id arrayPorts d Function.injective_id arrayPorts_injective
    (a := ⟨d.regs, d.stacks ∘ arrayPorts⟩)
    (b := ⟨readRegs d.regs 0 1 none,
      ArrayUpdatePrograms.replaceStacks earlier replacement rest (d.stacks ∘ arrayPorts)⟩) ht
  simpa only [arrayReplace, embed_array_input, embed_array_replace] using he

end SubexponentialSAT.SubexpJetCellProgram
namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

/-- The arithmetic controller and the dense serializer use the same four
stored words, including their order. -/
theorem flat_encode_eq_block (p D : ℕ) (a : SubexpSymbolicCost.QuarticCode p D) :
    SubexpFlatAdd.encode a = (SubexpSymbolicCost.quarticCodeBlockCode p D).block a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    SubexpSymbolicCost.quarticCodeBlockCode, SubexpSymbolicCost.recordBlockCode,
    SubexpSymbolicCost.wordBlockCode, SubexpSymbolicCost.quadToPair, List.append_assoc]

def regPorts : Fin 8 → Fin 16 := Fin.castAdd 8
def scalarPorts : Fin 20 → Fin 128 := Fin.castAdd 108

theorem regPorts_injective : Function.Injective regPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem scalarPorts_injective : Function.Injective scalarPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

def addCall : Code := .call
  (ProgramLinking.liftProgram SubexpFlatAdd.program regPorts scalarPorts)

def addOut (d : Data) (regs : Fin 8 → Bool) (result : List Bool) : Data :=
  ⟨fun i => Fin.addCases (m := 8) (n := 8) (motive := fun _ => Bool) regs
      (fun j => d.regs (Fin.natAdd 8 j)) i,
    Function.update (Function.update d.stacks 8 result) 9 []⟩

/-- The explicit state expression obtained by composing the eight services. -/
def updatedState (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool) : Data :=
  let d₁ := afterCopy d 103 113 0 1
  let d₂ := readOut d₁ old
  let d₃ := moveOut d₂ 112 9
  let d₄ := addOut d₃ regs result
  let d₅ := moveOut d₄ 8 112
  let d₆ := afterCopy d₅ 103 113 0 1
  let d₇ := replaceOut d₆ earlier result rest
  clearOut d₇ 112

theorem updatedState_stacks (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool)
    (h9 : d.stacks 9 = []) (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = []) :
    (updatedState d regs old result earlier rest).stacks =
      Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++ (result ++ rest)) := by
  funext j
  by_cases h8j : j = 8 <;> by_cases h9j : j = 9 <;>
    by_cases h102j : j = 102 <;> by_cases h112j : j = 112 <;> by_cases h113j : j = 113 <;>
    simp_all [updatedState, clearOut, replaceOut, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks ]

theorem updatedState_regs (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool) (i : Fin 8) :
    (updatedState d regs old result earlier rest).regs (Fin.natAdd 8 i) =
      d.regs (Fin.natAdd 8 i) := by
  have h0 : (Fin.natAdd 8 i : Fin 16) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 : (Fin.natAdd 8 i : Fin 16) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [updatedState, clearOut, replaceOut, addOut, moveOut, readOut, afterCopy,
    readRegs, h0, h1, Fin.addCases_right, Function.update_apply, -Fin.natAdd_eq_addNat]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

omit [Fact (Nat.Prime p)] in
/-- The concrete prepared zero is exactly the all-false fixed-width cell. -/
theorem encode_prepareZero :
    SubexpFlatAdd.encode (SubexpPreparedQuartic.prepareZero p μ).1 =
      List.replicate (4 * baseWidth p μ) false := by
  have hz (B : ℕ) : (SubexpModulusConstruction.normalizeRun B []).1 =
      List.replicate B false := by
    induction B with
    | zero => rfl
    | succ B ih => simp [SubexpModulusConstruction.normalizeRun, ih, List.replicate_succ]
  simp only [SubexpFlatAdd.encode, SubexpFlatAdd.quadWords, SubexpFlatAdd.flatten,
    SubexpPreparedQuartic.prepareZero, SubexpPreparedQuartic.literalWordRun,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, hz,
    ← List.replicate_add]
  congr 1
  omega

omit [Fact (Nat.Prime p)] in
theorem encode_replicate_prepareZero (D : ℕ) :
    ((List.replicate D (SubexpPreparedQuartic.prepareZero p μ).1).map
      SubexpFlatAdd.encode).flatten = List.replicate (D * (4 * baseWidth p μ)) false := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.replicate_succ, List.map_cons, List.flatten_cons, encode_prepareZero,
        ih, ← List.replicate_add]
      congr 1
      ring

theorem addCall_eval (d : Data) (a b : Quad (Word (baseWidth p μ)))
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpFlatAdd.ready (d.regs ∘ regPorts) M.bits
        (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b) width [] frame).stacks i) :
    ∃ n ≤ 25000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval addCall n d
        (addOut d regs' (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1)) := by
  obtain ⟨regs', n, hn, ht⟩ :=
    SubexpFlatAdd.program_runs_uniform p μ M (d.regs ∘ regPorts) a b width frame hwidth
  let left := SubexpFlatAdd.ready (d.regs ∘ regPorts) M.bits
    (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b) width [] frame
  let right := SubexpFlatAdd.ready regs' M.bits
    (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) [] width [] frame
  have hl : embedState regPorts scalarPorts d left = d := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intros; rfl
    · exact hsmall
    · intros; rfl
    · intros; rfl
  have hr : embedState regPorts scalarPorts d right =
      addOut d regs' (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1) := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intro i
      simp [addOut, right, SubexpFlatAdd.state, regPorts]
    · intro i
      have hi := hsmall i
      fin_cases i <;>
        simp [addOut, right, scalarPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state,
          SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> exact hi
    · intro j
      refine Fin.addCases (m := 8) (n := 8) ?_ ?_ j
      · intro i hi
        exact False.elim (hi ⟨i, rfl⟩)
      · intro i _
        simp [addOut, Fin.addCases_right, -Fin.natAdd_eq_addNat]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [scalarPorts] using h.symm⟩
      have h9 : j ≠ 9 := fun h => hj ⟨9, by simpa [scalarPorts] using h.symm⟩
      simp [addOut, h8, h9]
  have he := eval_call_lifted SubexpFlatAdd.program regPorts scalarPorts d
    regPorts_injective scalarPorts_injective (a := left) (b := right) ht
  exact ⟨n, hn, regs', by simpa only [addCall, hl, hr] using he⟩

def updateCell : Code :=
  .seq copyIndex (.seq arrayRead (.seq (moveForward 112 9) (.seq addCall
    (.seq (moveForward 8 112) (.seq copyIndex (.seq arrayReplace (clear 112)))))))

abbrev program : Program 16 128 (StructuredCalls.size updateCell + 1) :=
  StructuredCalls.compiled updateCell 8 102

def eventBudget (B I : ℕ) : ℕ :=
  25000 * (B + 1)^2 + I * (112 * B + 34) + 196 * B + 62

theorem eventBudget_polynomial (B I : ℕ) :
    eventBudget B I + 1 ≤ 30000 * (I + 1) * (B + 1)^2 := by
  have hi : 112 * B + 34 ≤ 500 * (B + 1)^2 := by nlinarith
  have hc : 196 * B + 63 ≤ 500 * (B + 1)^2 := by nlinarith
  have him := Nat.mul_le_mul_left I hi
  unfold eventBudget
  nlinarith [Nat.zero_le (I * (B + 1)^2)]

theorem eventBudget_of_index_le (B I D : ℕ) (hI : I ≤ D) :
    eventBudget B I + 1 ≤ 30000 * (D + 1) * (B + 1)^2 :=
  (eventBudget_polynomial B I).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hI 1)))

/-- Exact stack endpoint: only the consumed contribution and selected jet
cell change. The persistent index and all other caller stacks are preserved. -/
theorem updateCell_eval (d : Data) (a b : Quad (Word (baseWidth p μ)))
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (SubexpFlatAdd.encode b ++ rest))
    (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = 4 * baseWidth p μ)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hscalarWidth : scalarWidth.length = baseWidth p μ)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpFlatAdd.ready (d.regs ∘ regPorts) M.bits
        (SubexpFlatAdd.encode a) [] scalarWidth [] frame).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ eventBudget (baseWidth p μ) indexWord.length, ∃ e : Data,
      Eval updateCell n d e ∧
      e.stacks = Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++
          (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1 ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  let d₁ := afterCopy d 103 113 0 1
  have h₁ := copyIndex_eval d h114
  let d₂ := readOut d₁ (SubexpFlatAdd.encode b)
  have h₂ := arrayRead_eval d₁ earlier (SubexpFlatAdd.encode b) rest widthWord indexWord
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hs)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hw)
    (by simp [d₁, afterCopy, StackRoutines.copyStacks, hi, h113]) hiLen hrows
    (by simp [hwLen])
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h114)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h115)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h116)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h117)
  let d₃ := moveOut d₂ 112 9
  have h₃ := moveForward_eval d₂ 112 9 (by decide) (by decide) (by decide)
    (by simpa [d₂, d₁, readOut, afterCopy, StackRoutines.copyStacks] using h118)
  have hsmall₃ : ∀ i : Fin 20, d₃.stacks (scalarPorts i) =
      (SubexpFlatAdd.ready (d₃.regs ∘ regPorts) M.bits (SubexpFlatAdd.encode a)
        (SubexpFlatAdd.encode b) scalarWidth [] frame).stacks i := by
    intro i
    have h := hsmall i
    fin_cases i <;>
      simp [d₃, d₂, d₁, moveOut, readOut, afterCopy, StackRoutines.copyStacks,
        scalarPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod, h112] at h ⊢ <;> simp [h]
  obtain ⟨m, hm, regs', h₄⟩ := addCall_eval p μ M d₃ a b scalarWidth frame hscalarWidth hsmall₃
  let result := (SubexpPreparedQuartic.binaryAdd p μ M a b).1
  let d₄ := addOut d₃ regs' (SubexpFlatAdd.encode result)
  let d₅ := moveOut d₄ 8 112
  have h₅ := moveForward_eval d₄ 8 112 (by decide) (by decide) (by decide)
    (by simpa [d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h118)
  let d₆ := afterCopy d₅ 103 113 0 1
  have h₆ := copyIndex_eval d₅
    (by simpa [d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
  let d₇ := replaceOut d₆ earlier (SubexpFlatAdd.encode result) rest
  have h₇ := arrayReplace_eval d₆ earlier (SubexpFlatAdd.encode b)
    (SubexpFlatAdd.encode result) rest widthWord indexWord
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hs)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hw)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks, hi]) hiLen hrows (by simp [hwLen]) (by simp [hwLen])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h115)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h116)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h117)
  let d₈ := clearOut d₇ 112
  have h₈ := clear_eval d₇ 112
  have ht : Eval updateCell _ d d₈ :=
    Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq h₅
      (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  refine ⟨_, ?_, d₈, ht, ?_, ?_⟩
  · simp [eventBudget, d₇, d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut,
      replaceOut, afterCopy, StackRoutines.copyStacks, hi, h112, hwLen] at ⊢
    rw [hiLen]
    nlinarith [hm]
  · have h9 : d.stacks 9 = [] := by
      simpa [scalarPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod]
        using hsmall 9
    exact updatedState_stacks d regs' (SubexpFlatAdd.encode b)
      (SubexpFlatAdd.encode result) earlier rest h9 h112 h113
  · exact updatedState_regs d regs' (SubexpFlatAdd.encode b)
      (SubexpFlatAdd.encode result) earlier rest

/-- The packed-array theorem specialized to actual typed coefficient cells.
No decoder or abstract array callback is assumed. -/
theorem updateCell_typed_eval (d : Data) (a b : Quad (Word (baseWidth p μ)))
    (earlierCells suffix : List (Quad (Word (baseWidth p μ))))
    (widthWord indexWord scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hs : d.stacks 102 =
      ((earlierCells ++ b :: suffix).map SubexpFlatAdd.encode).flatten)
    (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlierCells.length)
    (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = 4 * baseWidth p μ)
    (hscalarWidth : scalarWidth.length = baseWidth p μ)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpFlatAdd.ready (d.regs ∘ regPorts) M.bits
        (SubexpFlatAdd.encode a) [] scalarWidth [] frame).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ eventBudget (baseWidth p μ) indexWord.length, ∃ e : Data,
      Eval updateCell n d e ∧
      e.stacks = Function.update (Function.update d.stacks 8 []) 102
        (((earlierCells ++ (SubexpPreparedQuartic.binaryAdd p μ M a b).1 :: suffix).map
          SubexpFlatAdd.encode).flatten) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  have hrows : ∀ row ∈ earlierCells.map SubexpFlatAdd.encode, row.length = widthWord.length := by
    intro row hrow
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hrow
    simp [hwLen]
  have harray : d.stacks 102 = (earlierCells.map SubexpFlatAdd.encode).flatten ++
      (SubexpFlatAdd.encode b ++ (suffix.map SubexpFlatAdd.encode).flatten) := by
    simpa only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons] using hs
  obtain ⟨n, hn, e, he, hst, hr⟩ := updateCell_eval p μ M d a b
    (earlierCells.map SubexpFlatAdd.encode) (suffix.map SubexpFlatAdd.encode).flatten
    widthWord indexWord scalarWidth frame harray hi
    (by simpa only [List.length_map] using hiLen) hw hwLen hrows hscalarWidth hsmall
    h112 h113 h114 h115 h116 h117 h118
  refine ⟨n, hn, e, he, ?_, hr⟩
  simpa only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons] using hst

omit [Fact (Nat.Prime p)] in
theorem updated_cells_length (a b : Quad (Word (baseWidth p μ)))
    (earlierCells suffix : List (Quad (Word (baseWidth p μ)))) :
    (earlierCells ++ (SubexpPreparedQuartic.binaryAdd p μ M a b).1 :: suffix).length =
      (earlierCells ++ b :: suffix).length := by simp

theorem program_trace {n : ℕ} {d e : Data} (h : Eval updateCell n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  StructuredCalls.compiled_halt_trace h 8 102

theorem result_stack_frame {d e : Data} {updatedArray : List Bool}
    (h : e.stacks = Function.update (Function.update d.stacks 8 []) 102 updatedArray)
    (j : Fin 128) (h8 : j ≠ 8) (h102 : j ≠ 102) : e.stacks j = d.stacks j := by
  rw [h]
  simp [h8, h102]

theorem result_caller_frame {d e : Data} {updatedArray : List Bool}
    (h : e.stacks = Function.update (Function.update d.stacks 8 []) 102 updatedArray)
    (j : Fin 128) (hj : 100 ≤ j.val) (h102 : j ≠ 102) : e.stacks j = d.stacks j := by
  apply result_stack_frame h j _ h102
  intro he
  subst j
  norm_num [Fin.coe_ofNat_eq_mod] at hj

theorem program_call {n : ℕ} {d e : Data} (h : Eval updateCell n d e) :
    Eval (.call program) (n + 1) d e :=
  Eval.call program (program_trace h)

theorem program_primitive {n B : ℕ} {d e : Data}
    (h : Eval updateCell n d e) (hn : n ≤ B) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * (B + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) := by
  obtain ⟨steps, hsteps, ht⟩ := primitive_trace program (program_trace h)
  exact ⟨steps, hsteps.trans (Nat.mul_le_mul_left _ (by omega)), ht⟩

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
