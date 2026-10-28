import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatData
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul
import OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

def regPort (i : Fin 8) : Fin 16 := ⟨i.val, by omega⟩
def highPort (i : Fin 77) : Fin 256 := ⟨128 + i.val, by omega⟩
def lowPort (i : Fin 128) : Fin 256 := ⟨i.val, by omega⟩

theorem regPort_injective : Function.Injective regPort := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem highPort_injective : Function.Injective highPort := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun i : Fin 256 => i.val) h
  dsimp [highPort] at hv
  omega

theorem lowPort_injective : Function.Injective lowPort := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 256 => i.val) h)

def replaceRegs (d : Data) (r : Fin 8 → Bool) : Fin 16 → Bool :=
  fun i => if h : i.val < 8 then r ⟨i.val, h⟩ else d.regs i

@[simp] theorem replaceRegs_low (d : Data) (r : Fin 8 → Bool) (i : Fin 8) :
    replaceRegs d r (regPort i) = r i := by simp [replaceRegs, regPort]

@[simp] theorem replaceRegs_high (d : Data) (r : Fin 8 → Bool) (i : Fin 8) :
    replaceRegs d r (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i) := by
  simp [replaceRegs]

def mulOut {B : ℕ} (d : Data) (r : Fin 8 → Bool) (result : Quad (Word B)) : Data :=
  ⟨replaceRegs d r,
    Function.update
      (Function.update (Function.update d.stacks (highPort 70) []) (highPort 71) [])
      (highPort 72) (SubexpQuarticFlatMul.flat result)⟩

def moveProduct : Code :=
  .seq (.call (StackRoutines.transferProgram (200 : Fin 256) 119 (0 : Fin 16) 1))
    (.call (StackRoutines.transferProgram (119 : Fin 256) 8 (0 : Fin 16) 1))

def moveOut (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 200 []) 8 (d.stacks 200)⟩

theorem moveProduct_eval (d : Data) (h8 : d.stacks 8 = []) (h119 : d.stacks 119 = []) :
    Eval moveProduct (6 * (d.stacks 200).length + 6) d (moveOut d) := by
  have h1 := transfer_eval d (200 : Fin 256) 119 (0 : Fin 16) 1 (by decide) (by decide)
  have h2 := transfer_eval (afterTransfer d 200 119 0 1)
    (119 : Fin 256) 8 (0 : Fin 16) 1 (by decide) (by decide)
  have he : afterTransfer (afterTransfer d 200 119 0 1) 119 8 0 1 = moveOut d := by
    apply state_ext
    · simp [afterTransfer, moveOut, StackRoutines.readRegs_reset]
    · funext j
      by_cases h8j : j = 8
      · subst j
        simp [afterTransfer, moveOut, StackRoutines.transferStacks, h8, h119]
      · by_cases h119j : j = 119
        · subst j
          simp [afterTransfer, moveOut, StackRoutines.transferStacks, h119]
        · simp [afterTransfer, moveOut, StackRoutines.transferStacks, h8j, h119j]
  have hlen : ((afterTransfer d 200 119 0 1).stacks 119).length =
      (d.stacks 200).length := by simp [afterTransfer, StackRoutines.transferStacks, h119]
  simpa only [moveProduct, he, hlen,
    show ∀ n : ℕ, (3*n+3)+(3*n+3)=6*n+6 by omega] using h1.seq h2

@[simp] theorem moveOut_regs_high (d : Data) (i : Fin 8) :
    (moveOut d).regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i) := by
  have h0 : Fin.natAdd 8 i ≠ (0 : Fin 16) := by
    intro h
    have := congrArg (fun j : Fin 16 => j.val) h
    simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at this
    omega
  have h1 : Fin.natAdd 8 i ≠ (1 : Fin 16) := by
    intro h
    have := congrArg (fun j : Fin 16 => j.val) h
    simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at this
    omega
  simp only [moveOut, readRegs, Function.update_of_ne h0, Function.update_of_ne h1]

@[simp] theorem mulOut_regs_high {B : ℕ} (d : Data) (r : Fin 8 → Bool)
    (result : Quad (Word B)) (i : Fin 8) :
    (mulOut d r result).regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i) := by
  exact replaceRegs_high d r i

theorem embed_high_input (d : Data) (words : Fin 77 → List Bool)
    (hwords : ∀ i, d.stacks (highPort i) = words i) :
    embedState regPort highPort d ⟨d.regs ∘ regPort, words⟩ = d := by
  apply embedState_eq_of_ports regPort highPort d d _ regPort_injective highPort_injective
  · intro i; rfl
  · intro i hi; rfl
  · exact hwords
  · intro i hi; rfl

theorem embed_high_output {B : ℕ} (d : Data) (r : Fin 8 → Bool)
    (result : Quad (Word B)) (words : Fin 77 → List Bool)
    (hwords : ∀ i, d.stacks (highPort i) = words i) :
    embedState regPort highPort d
      ⟨r, Function.update (Function.update (Function.update words 70 []) 71 [])
        72 (SubexpQuarticFlatMul.flat result)⟩ = mulOut d r result := by
  apply embedState_eq_of_ports regPort highPort d _ _ regPort_injective highPort_injective
  · intro i
    exact replaceRegs_low d r i
  · intro i hi
    have hn : ¬ i.val < 8 := by
      intro h
      exact hi ⟨⟨i.val, h⟩, by apply Fin.ext; rfl⟩
    simp [mulOut, replaceRegs, hn]
  · intro i
    simp [mulOut, Function.update_apply, highPort_injective.eq_iff, hwords]
  · intro i hi
    have h70 : i ≠ highPort 70 := fun h => hi ⟨70, h.symm⟩
    have h71 : i ≠ highPort 71 := fun h => hi ⟨71, h.symm⟩
    have h72 : i ≠ highPort 72 := fun h => hi ⟨72, h.symm⟩
    simp [mulOut, h70, h71, h72]

def lowState (d : Data) : State 16 128 := ⟨d.regs, d.stacks ∘ lowPort⟩

theorem embed_low_input (d : Data) : embedState id lowPort d (lowState d) = d := by
  apply embedState_eq_of_ports id lowPort d d _ Function.injective_id lowPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; rfl
  · intro i hi; rfl

theorem embed_low_output (d : Data) (e : State 16 128) (record : List Bool)
    (he : e.stacks = Function.update (Function.update (lowState d).stacks 8 []) 102 record) :
    embedState id lowPort d e =
      (⟨e.regs, Function.update (Function.update d.stacks (lowPort 8) [])
        (lowPort 102) record⟩ : Data) := by
  apply embedState_eq_of_ports id lowPort d _ _ Function.injective_id lowPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    rw [he]
    simp [lowState, Function.update_apply, lowPort_injective.eq_iff]
  · intro i hi
    have h8 : i ≠ lowPort 8 := fun h => hi ⟨8, h.symm⟩
    have h102 : i ≠ lowPort 102 := fun h => hi ⟨102, h.symm⟩
    simp [h8, h102]

theorem low_ne_high (i : Fin 128) (j : Fin 77) : lowPort i ≠ highPort j := by
  intro h
  have hv := congrArg (fun j : Fin 256 => j.val) h
  dsimp [lowPort, highPort] at hv
  omega

theorem mul_move_low_frame {B : ℕ} (d : Data) (r : Fin 8 → Bool)
    (result : Quad (Word B)) (j : Fin 128) (hj : j ≠ 8) :
    (lowState (moveOut (mulOut d r result))).stacks j = d.stacks (lowPort j) := by
  have h8 : lowPort j ≠ 8 := by
    intro h
    apply hj
    apply lowPort_injective
    exact h
  have h200 : lowPort j ≠ 200 := low_ne_high j 72
  simp [lowState, moveOut, mulOut, h8, h200, low_ne_high]

theorem finish_stacks {B : ℕ} (d : Data) (r : Fin 8 → Bool)
    (product : Quad (Word B)) (record : List Bool)
    (h8 : d.stacks 8 = []) (h200 : d.stacks 200 = []) :
    Function.update
        (Function.update (moveOut (mulOut d r product)).stacks (lowPort 8) [])
        (lowPort 102) record =
      Function.update (Function.update (Function.update d.stacks 198 []) 199 [])
        102 record := by
  funext j
  by_cases hj : j = 102
  · subst j
    simp [lowPort]
  · by_cases hj8 : j = 8
    · subst j
      simp [lowPort, moveOut, mulOut, highPort, h8]
    · by_cases hj200 : j = 200
      · subst j
        simp [lowPort, moveOut, mulOut, highPort, h200]
      · simp [lowPort, moveOut, mulOut, highPort, hj, hj8, hj200]

theorem pair_budget (B I n₁ n₃ : ℕ)
    (h₁ : n₁ ≤ 400000 * (B + 1)^2)
    (h₃ : n₃ + 1 ≤ 30000 * (I + 1) * (B + 1)^2) :
    n₁ + ((6 * (4 * B) + 6) + (n₃ + 1)) ≤
      500000 * (I + 1) * (B + 1)^2 := by
  have hmove : 6 * (4 * B) + 6 ≤ 1000 * (B + 1)^2 := by nlinarith
  have hscale : (B + 1)^2 ≤ (I + 1) * (B + 1)^2 :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h₁' : n₁ ≤ 400000 * ((I + 1) * (B + 1)^2) :=
    h₁.trans (Nat.mul_le_mul_left _ hscale)
  have hmove' : 6 * (4 * B) + 6 ≤ 1000 * ((I + 1) * (B + 1)^2) :=
    hmove.trans (Nat.mul_le_mul_left _ hscale)
  have h₃' : n₃ + 1 ≤ 30000 * ((I + 1) * (B + 1)^2) := by
    simpa only [Nat.mul_assoc] using h₃
  calc
    _ ≤ 400000 * ((I + 1) * (B + 1)^2) +
        (1000 * ((I + 1) * (B + 1)^2) + 30000 * ((I + 1) * (B + 1)^2)) :=
      Nat.add_le_add h₁' (Nat.add_le_add hmove' h₃')
    _ = 431000 * ((I + 1) * (B + 1)^2) := by ring
    _ ≤ 500000 * ((I + 1) * (B + 1)^2) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatAdd.encode a := by
  cases a
  simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

theorem mul_move_scalar_ready {B : ℕ} (d : Data) (r : Fin 8 → Bool)
    (product : Quad (Word B)) (modulus scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (h : ∀ i : Fin 20, d.stacks (lowPort (SubexpJetCellProgram.scalarPorts i)) =
      (SubexpFlatAdd.ready r modulus [] [] scalarWidth [] frame).stacks i) :
    ∀ i : Fin 20,
      (lowState (moveOut (mulOut d r product))).stacks
          (SubexpJetCellProgram.scalarPorts i) =
        (SubexpFlatAdd.ready r modulus (SubexpFlatAdd.encode product) []
          scalarWidth [] frame).stacks i := by
  intro i
  have hi := h i
  fin_cases i <;>
    simp [lowState, moveOut, mulOut, highPort, lowPort,
      SubexpJetCellProgram.scalarPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.stacks, flat_eq_encode, Fin.addCases] at hi ⊢ <;> exact hi

def multiply : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticFlatMul.program regPort highPort)

def accumulate : Code :=
  .call (ProgramLinking.liftProgram SubexpJetCellProgram.program id lowPort)

def command : Code := .seq multiply (.seq moveProduct accumulate)

def program := compiled command (198 : Fin 256) 102

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem multiply_eval (d : Data) (t a b : Quad (Word (baseWidth p μ)))
    (scalarWidth : List Bool) (hw : scalarWidth.length = baseWidth p μ)
    (hh : ∀ i, d.stacks (highPort i) =
      SubexpQuarticFlatMul.initialStore M.bits scalarWidth t a b i) :
    ∃ n r, n ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval multiply n d (mulOut d r (SubexpPreparedQuartic.binaryMul p μ M t a b).1) := by
  obtain ⟨r, n, hn, ht⟩ := SubexpQuarticFlatMul.program_run p μ M t a b scalarWidth hw
    (d.regs ∘ regPort)
  have he := eval_call_lifted SubexpQuarticFlatMul.program regPort highPort d
    regPort_injective highPort_injective
    (a := ⟨d.regs ∘ regPort, SubexpQuarticFlatMul.initialStore M.bits scalarWidth t a b⟩)
    (b := ⟨r, SubexpQuarticFlatMul.finalStore M.bits scalarWidth t
      (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩) ht
  rw [embed_high_input d _ hh] at he
  rw [SubexpQuarticFlatMul.finalStore_updates M.bits scalarWidth t a b] at he
  rw [embed_high_output d r _ _ hh] at he
  exact ⟨n, r, hn, he⟩

/-- Readiness is a concrete assertion about the current tapes and encoded
array. The operand, coefficient, and index values remain runtime data. -/
structure Ready (d : Data) (t a b c : Quad (Word (baseWidth p μ)))
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  high : ∀ i, d.stacks (highPort i) =
    SubexpQuarticFlatMul.initialStore M.bits scalarWidth t a b i
  low : ∀ i : Fin 20, d.stacks (lowPort (SubexpJetCellProgram.scalarPorts i)) =
    (SubexpFlatAdd.ready (d.regs ∘ regPort) M.bits [] [] scalarWidth [] frame).stacks i
  array : d.stacks 102 = earlier.flatten ++ (SubexpFlatAdd.encode c ++ rest)
  index : d.stacks 103 = indexWord
  indexLength : indexWord.length = earlier.length
  width : d.stacks 104 = widthWord
  widthLength : widthWord.length = 4 * baseWidth p μ
  rows : ∀ row ∈ earlier, row.length = widthWord.length
  scalarWidthLength : scalarWidth.length = baseWidth p μ
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → d.stacks j = []

def result (t a b c : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M
    (SubexpPreparedQuartic.binaryMul p μ M t a b).1 c).1

/-- Actual product, order-preserving transfer, and packed-cell accumulation.
Only the two consumed operands and the selected accumulator cell change. -/
theorem command_eval (d : Data) (t a b c : Quad (Word (baseWidth p μ)))
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p μ M d t a b c earlier rest widthWord indexWord scalarWidth frame) :
    ∃ n e, n ≤ 500000 * (indexWord.length + 1) * (baseWidth p μ + 1)^2 ∧
      Eval command n d e ∧
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 198 []) 199 []) 102
        (earlier.flatten ++ (SubexpFlatAdd.encode (result p μ M t a b c) ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  let product := (SubexpPreparedQuartic.binaryMul p μ M t a b).1
  obtain ⟨n1, r1, hn1, he1⟩ := multiply_eval p μ M d t a b scalarWidth H.scalarWidthLength H.high
  let d1 := mulOut d r1 product
  let d2 := moveOut d1
  have h8 : d.stacks 8 = [] := by
    simpa [lowPort, SubexpJetCellProgram.scalarPorts, SubexpFlatAdd.ready,
      SubexpFlatAdd.state, SubexpFlatAdd.stacks, Fin.addCases] using H.low 8
  have h200 : d.stacks 200 = [] := by
    simpa [highPort, SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.bankStore]
      using H.high 72
  have h18 : d1.stacks 8 = [] := by simp [d1, mulOut, highPort, h8]
  have h119 : d1.stacks 119 = [] := by
    simpa [d1, mulOut, highPort] using H.work 119 (by decide) (by decide)
  have he2 := moveProduct_eval d1 h18 h119
  have hlen : (d1.stacks 200).length = 4 * baseWidth p μ := by
    simp [d1, mulOut, highPort]
  have hf (j : Fin 128) (hj : j ≠ 8) :
      (lowState d2).stacks j = d.stacks (lowPort j) :=
    mul_move_low_frame d r1 product j hj
  have hsmall : ∀ i : Fin 20, (lowState d2).stacks (SubexpJetCellProgram.scalarPorts i) =
      (SubexpFlatAdd.ready ((lowState d2).regs ∘ SubexpJetCellProgram.regPorts) M.bits
        (SubexpFlatAdd.encode product) [] scalarWidth [] frame).stacks i := by
    exact mul_move_scalar_ready d r1 product M.bits scalarWidth frame H.low
  have hp (i : Fin 128) : lowPort i = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rfl
  obtain ⟨n3, hn3, e3, he3, hs3, hr3⟩ := SubexpJetCellProgram.updateCell_eval p μ M
    (lowState d2) product c earlier rest widthWord indexWord scalarWidth frame
    (by rw [hf 102 (by decide), hp]; exact H.array)
    (by rw [hf 103 (by decide), hp]; exact H.index) H.indexLength
    (by rw [hf 104 (by decide), hp]; exact H.width) H.widthLength H.rows
    H.scalarWidthLength hsmall
    (by rw [hf 112 (by decide), hp]; exact H.work 112 (by decide) (by decide))
    (by rw [hf 113 (by decide), hp]; exact H.work 113 (by decide) (by decide))
    (by rw [hf 114 (by decide), hp]; exact H.work 114 (by decide) (by decide))
    (by rw [hf 115 (by decide), hp]; exact H.work 115 (by decide) (by decide))
    (by rw [hf 116 (by decide), hp]; exact H.work 116 (by decide) (by decide))
    (by rw [hf 117 (by decide), hp]; exact H.work 117 (by decide) (by decide))
    (by rw [hf 118 (by decide), hp]; exact H.work 118 (by decide) (by decide))
  let record := earlier.flatten ++ (SubexpFlatAdd.encode (result p μ M t a b c) ++ rest)
  let e : Data := ⟨e3.regs, Function.update (Function.update d2.stacks (lowPort 8) [])
    (lowPort 102) record⟩
  have hcall := eval_call_lifted SubexpJetCellProgram.program id lowPort d2
    Function.injective_id lowPort_injective
    (a := lowState d2) (b := e3) (SubexpJetCellProgram.program_trace he3)
  rw [embed_low_input, embed_low_output d2 e3 record hs3] at hcall
  have hbound3 : n3 + 1 ≤ 30000 * (indexWord.length + 1) * (baseWidth p μ + 1)^2 :=
    (Nat.add_le_add_right hn3 1).trans (SubexpJetCellProgram.eventBudget_polynomial _ _)
  refine ⟨n1 + ((6 * (d1.stacks 200).length + 6) + (n3 + 1)), e, ?_,
    he1.seq (he2.seq hcall), ?_, ?_⟩
  · rw [hlen]
    exact pair_budget _ _ _ _ hn1 hbound3
  · exact finish_stacks d r1 product record h8 h200
  · intro i
    change e3.regs (Fin.natAdd 8 i) = _
    rw [hr3 i]
    exact (moveOut_regs_high d1 i).trans (mulOut_regs_high d r1 product i)

/-- The pair service as an actual halted finite bit program. -/
theorem run_value (d : Data) (t a b c : Quad (Word (baseWidth p μ)))
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p μ M d t a b c earlier rest widthWord indexWord scalarWidth frame) :
    ∃ e : Data,
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 198 []) 199 []) 102
        (earlier.flatten ++ (SubexpFlatAdd.encode (result p μ M t a b c) ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) ∧
      BitProgram.RunsIn program
        (600000 * (indexWord.length + 1) * (baseWidth p μ + 1)^2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := command_eval p μ M d t a b c earlier rest
    widthWord indexWord scalarWidth frame H
  refine ⟨e, hs, hr, n + 1, ?_, compiled_halt_trace he 198 102⟩
  have hp : 0 < (indexWord.length + 1) * (baseWidth p μ + 1)^2 := by positivity
  simp only [Nat.mul_assoc] at hn ⊢
  omega

/-- The same concrete routine in the primitive machine model. The compiler
overhead is a fixed constant because the pair program is fixed. -/
theorem primitive_value (d : Data) (t a b c : Quad (Word (baseWidth p μ)))
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (H : Ready p μ M d t a b c earlier rest widthWord indexWord scalarWidth frame) :
    ∃ e : Data,
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 198 []) 199 []) 102
        (earlier.flatten ++ (SubexpFlatAdd.encode (result p μ M t a b c) ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) ∧
      SubexpQuarticFlatMul.PrimitiveRunsIn program
        (primitiveOverhead program *
          (600000 * (indexWord.length + 1) * (baseWidth p μ + 1)^2))
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨e, hs, hr, he⟩ := run_value p μ M d t a b c earlier rest
    widthWord indexWord scalarWidth frame H
  exact ⟨e, hs, hr, SubexpQuarticFlatMul.primitiveRunsIn_of_runsIn program he⟩

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
