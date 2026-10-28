import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! A concrete, preserving caller for the fixed-width exponent-key adder. -/

namespace SubexponentialSAT.SubexpDenseKeyProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def copy (src dst : Fin 128) : Code :=
  .call (StackRoutines.copyProgram src dst 24 0 1)

def copied (src dst : Fin 128) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 128) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 24) (hd : (24 : Fin 128) ≠ dst)
    (ht : d.stacks 24 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 24 0 1 hsd hs hd (by decide)
    d.regs d.stacks ht

def clear (src : Fin 128) : Code := .call (StackRoutines.clearProgram src 0 1)

def cleared (src : Fin 128) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 128) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src 0 1 d.regs d.stacks

def keyRegisters : Fin 2 → Fin 16 := Fin.castAdd 14
def keyPorts : Fin 4 → Fin 128 := ![0, 1, 2, 16]

theorem keyRegisters_injective : Function.Injective keyRegisters := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem keyPorts_injective : Function.Injective keyPorts := by decide

def keyCall : Code := .call
  (ProgramLinking.liftProgram SubexpExponentProgram.keyAddProgram keyRegisters keyPorts)

def afterKey (d : Data) (regs : Fin 2 → Bool) (left right output : List Bool) : Data :=
  ⟨Function.update (Function.update d.regs 0 (regs 0)) 1 (regs 1),
    Function.update (Function.update (Function.update (Function.update d.stacks
      0 left) 1 right) 2 []) 16 output⟩

private theorem embed_key (d : Data) (regs : Fin 2 → Bool)
    (left right count output : List Bool) :
    embedState keyRegisters keyPorts d
      ⟨regs, SubexpExponentProgram.keyStacks left right count output⟩ =
      ⟨Function.update (Function.update d.regs 0 (regs 0)) 1 (regs 1),
        Function.update (Function.update (Function.update (Function.update d.stacks
          0 left) 1 right) 2 count) 16 output⟩ := by
  apply embedState_eq_of_ports _ _ _ _ _ keyRegisters_injective keyPorts_injective
  · intro i; fin_cases i <;> simp [keyRegisters]
  · intro i hi
    have h₀ : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h₁ : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    simp [h₀, h₁]
  · intro i; fin_cases i <;> simp [keyPorts, SubexpExponentProgram.keyStacks]
  · intro i hi
    have h₀ : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h₁ : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h₂ : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
    have h₁₆ : i ≠ 16 := fun h => hi ⟨3, h.symm⟩
    simp [h₀, h₁, h₂, h₁₆]

theorem keyCall_eval (d : Data) (left right : List Bool) (width : ℕ)
    (h₀ : d.stacks 0 = left) (h₁ : d.stacks 1 = right)
    (h₂ : d.stacks 2 = List.replicate width true) :
    ∃ regs, Eval keyCall (SubexpExponentProgram.rounds width left right).ticks d
      (afterKey d regs (SubexpExponentProgram.rounds width left right).left
        (SubexpExponentProgram.rounds width left right).right
        ((SubexpExponentProgram.normalizedBits width left right).reverse ++ d.stacks 16)) := by
  obtain ⟨regs, ht⟩ := SubexpExponentProgram.keyAdd_trace width
    (fun i => d.regs (keyRegisters i)) left right (d.stacks 16)
  change Trace SubexpExponentProgram.keyAddProgram _
    ((⟨fun i => d.regs (keyRegisters i), SubexpExponentProgram.keyStacks
      left right (List.replicate width true) (d.stacks 16)⟩ :
        StructuredProgram.State 2 4).withPC (some SubexpExponentProgram.keyAddProgram.entry))
    ((⟨regs, SubexpExponentProgram.keyStacks
      (SubexpExponentProgram.rounds width left right).left
      (SubexpExponentProgram.rounds width left right).right []
      ((SubexpExponentProgram.normalizedBits width left right).reverse ++ d.stacks 16)⟩ :
        StructuredProgram.State 2 4).withPC none) at ht
  have hc := eval_call_lifted SubexpExponentProgram.keyAddProgram keyRegisters keyPorts d
    keyRegisters_injective keyPorts_injective ht
  rw [embed_key, embed_key] at hc
  have hb : (⟨Function.update (Function.update d.regs 0 (d.regs (keyRegisters 0))) 1
        (d.regs (keyRegisters 1)),
      Function.update (Function.update (Function.update (Function.update d.stacks
        0 left) 1 right) 2 (List.replicate width true)) 16 (d.stacks 16)⟩ : Data) = d := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [keyRegisters]
    · rw [← h₀, ← h₁, ← h₂]
      simp
  rw [hb] at hc
  exact ⟨regs, hc⟩

private theorem advance_lengths (left right : List Bool) :
    (SubexpExponentProgram.advance left right).left.length ≤ left.length ∧
      (SubexpExponentProgram.advance left right).right.length ≤ right.length := by
  cases left with
  | nil => simp [SubexpExponentProgram.advance]
  | cons b xs =>
    cases b with
    | true => simp [SubexpExponentProgram.advance]
    | false =>
      cases right with
      | nil => simp [SubexpExponentProgram.advance]
      | cons b ys => cases b <;> simp [SubexpExponentProgram.advance]

theorem rounds_lengths (width : ℕ) (left right : List Bool) :
    (SubexpExponentProgram.rounds width left right).left.length ≤ left.length ∧
      (SubexpExponentProgram.rounds width left right).right.length ≤ right.length := by
  induction width generalizing left right with
  | zero => simp [SubexpExponentProgram.rounds]
  | succ n ih =>
    have ha := advance_lengths left right
    have hr := ih (SubexpExponentProgram.advance left right).left
      (SubexpExponentProgram.advance left right).right
    simp only [SubexpExponentProgram.rounds]
    exact ⟨hr.1.trans ha.1, hr.2.trans ha.2⟩

/-- The masters are 93/95 and unary width 92. Work 0/1/2/24 is restored;
the normalized sum is prepended, reversed, to the output on 16. -/
def addKeys : Code :=
  .seq (copy 93 0) (.seq (copy 95 1) (.seq (copy 92 2)
    (.seq keyCall (.seq (clear 0) (clear 1)))))

def program := StructuredCalls.compiled addKeys 93 16

theorem addKeys_eval_framed (d : Data) (left right : List Bool) (width : ℕ)
    (hl : d.stacks 93 = left) (hr : d.stacks 95 = right)
    (hw : d.stacks 92 = List.replicate width true)
    (h₀ : d.stacks 0 = []) (h₁ : d.stacks 1 = []) (h₂ : d.stacks 2 = [])
    (ht : d.stacks 24 = []) :
    ∃ ticks e, ticks ≤ 9 * (left.length + right.length) + 19 * width + 24 ∧
      Eval addKeys ticks d e ∧
      e.stacks = Function.update d.stacks 16
        ((SubexpExponentProgram.normalizedBits width left right).reverse ++ d.stacks 16) ∧
      (∀ i, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  let a := copied 93 0 d
  let b := copied 95 1 a
  let c := copied 92 2 b
  have hA := copy_eval 93 0 d (by decide) (by decide) (by decide) ht
  have hB := copy_eval 95 1 a (by decide) (by decide) (by decide) (by
    simp [a, copied, StackRoutines.copyStacks, ht])
  have hC := copy_eval 92 2 b (by decide) (by decide) (by decide) (by
    simp [b, a, copied, StackRoutines.copyStacks, ht])
  have hc₀ : c.stacks 0 = left := by
    simp [c, b, a, copied, StackRoutines.copyStacks, hl, h₀]
  have hc₁ : c.stacks 1 = right := by
    simp [c, b, a, copied, StackRoutines.copyStacks, hr, h₁]
  have hc₂ : c.stacks 2 = List.replicate width true := by
    simp [c, b, a, copied, StackRoutines.copyStacks, hw, h₂]
  obtain ⟨regs, hK⟩ := keyCall_eval c left right width hc₀ hc₁ hc₂
  let k := afterKey c regs (SubexpExponentProgram.rounds width left right).left
    (SubexpExponentProgram.rounds width left right).right
    ((SubexpExponentProgram.normalizedBits width left right).reverse ++ c.stacks 16)
  have hD := clear_eval 0 k
  have hE := clear_eval 1 (cleared 0 k)
  refine ⟨_, cleared 1 (cleared 0 k), ?_, hA.seq (hB.seq (hC.seq (hK.seq (hD.seq hE)))), ?_, ?_⟩
  · have hlens := rounds_lengths width left right
    have htime := SubexpExponentProgram.rounds_ticks_le width left right
    simp only [a, b, k, copied, cleared, afterKey, StackRoutines.copyStacks,
      Function.update_self, Function.update_of_ne (by decide : (95 : Fin 128) ≠ 0),
      Function.update_of_ne (by decide : (92 : Fin 128) ≠ 1),
      Function.update_of_ne (by decide : (92 : Fin 128) ≠ 0),
      Function.update_of_ne (by decide : (1 : Fin 128) ≠ 0),
      Function.update_of_ne (by decide : (0 : Fin 128) ≠ 16),
      Function.update_of_ne (by decide : (0 : Fin 128) ≠ 2),
      Function.update_of_ne (by decide : (0 : Fin 128) ≠ 1),
      Function.update_of_ne (by decide : (1 : Fin 128) ≠ 16),
      Function.update_of_ne (by decide : (1 : Fin 128) ≠ 2), hl, hr, hw,
      List.length_replicate]
    omega
  · funext i
    by_cases hi₀ : i = 0 <;> by_cases hi₁ : i = 1 <;>
      by_cases hi₂ : i = 2 <;> by_cases hi₁₆ : i = 16 <;>
      simp_all [k, c, b, a, cleared, afterKey, copied, StackRoutines.copyStacks]
  · intro i h0 h1
    simp [k, c, b, a, cleared, afterKey, copied, readRegs, h0, h1]

theorem addKeys_eval (d : Data) (left right : List Bool) (width : ℕ)
    (hl : d.stacks 93 = left) (hr : d.stacks 95 = right)
    (hw : d.stacks 92 = List.replicate width true)
    (h₀ : d.stacks 0 = []) (h₁ : d.stacks 1 = []) (h₂ : d.stacks 2 = [])
    (ht : d.stacks 24 = []) :
    ∃ ticks e, ticks ≤ 9 * (left.length + right.length) + 19 * width + 24 ∧
      Eval addKeys ticks d e ∧
      e.stacks = Function.update d.stacks 16
        ((SubexpExponentProgram.normalizedBits width left right).reverse ++ d.stacks 16) := by
  obtain ⟨n, e, hn, he, hs, _⟩ := addKeys_eval_framed d left right width hl hr hw h₀ h₁ h₂ ht
  exact ⟨n, e, hn, he, hs⟩

theorem fixedKey_eval_framed {D : ℕ} (d : Data) (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b)
    (hl : d.stacks 93 = SubexpSymbolicCost.fixedKey a)
    (hr : d.stacks 95 = SubexpSymbolicCost.fixedKey b)
    (hw : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (h₀ : d.stacks 0 = []) (h₁ : d.stacks 1 = []) (h₂ : d.stacks 2 = [])
    (ht : d.stacks 24 = []) :
    ∃ ticks e, ticks ≤ 40 * SubexpSymbolicCost.indexBits D + 39 ∧
      Eval addKeys ticks d e ∧
      e.stacks = Function.update d.stacks 16
        ((SubexpSymbolicCost.fixedKey (a + b)).reverse ++ d.stacks 16) ∧
      (∀ i, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  obtain ⟨ticks, e, hbound, he, hstacks, hregs⟩ := addKeys_eval_framed d
    (SubexpSymbolicCost.fixedKey a) (SubexpSymbolicCost.fixedKey b)
    (SubexpSymbolicCost.indexBits D) hl hr hw h₀ h₁ h₂ ht
  rw [SubexpSymbolicCost.fixedKey_length a ha, SubexpSymbolicCost.fixedKey_length b hb]
    at hbound
  rw [SubexpExponentProgram.normalizedBits_fixedKey a b ha hb] at hstacks
  exact ⟨ticks, e, by omega, he, hstacks, hregs⟩

theorem fixedKey_eval {D : ℕ} (d : Data) (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b)
    (hl : d.stacks 93 = SubexpSymbolicCost.fixedKey a)
    (hr : d.stacks 95 = SubexpSymbolicCost.fixedKey b)
    (hw : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (h₀ : d.stacks 0 = []) (h₁ : d.stacks 1 = []) (h₂ : d.stacks 2 = [])
    (ht : d.stacks 24 = []) :
    ∃ ticks e, ticks ≤ 40 * SubexpSymbolicCost.indexBits D + 39 ∧
      Eval addKeys ticks d e ∧
      e.stacks = Function.update d.stacks 16
        ((SubexpSymbolicCost.fixedKey (a + b)).reverse ++ d.stacks 16) := by
  obtain ⟨ticks, e, hbound, he, hstacks⟩ := addKeys_eval d
    (SubexpSymbolicCost.fixedKey a) (SubexpSymbolicCost.fixedKey b)
    (SubexpSymbolicCost.indexBits D) hl hr hw h₀ h₁ h₂ ht
  rw [SubexpSymbolicCost.fixedKey_length a ha, SubexpSymbolicCost.fixedKey_length b hb]
    at hbound
  rw [SubexpExponentProgram.normalizedBits_fixedKey a b ha hb] at hstacks
  exact ⟨ticks, e, by omega, he, hstacks⟩

theorem fixedKey_runsIn {D : ℕ} (d : Data) (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b)
    (hl : d.stacks 93 = SubexpSymbolicCost.fixedKey a)
    (hr : d.stacks 95 = SubexpSymbolicCost.fixedKey b)
    (hw : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (h₀ : d.stacks 0 = []) (h₁ : d.stacks 1 = []) (h₂ : d.stacks 2 = [])
    (ht : d.stacks 24 = []) :
    ∃ e : Data, RunsIn program (40 * SubexpSymbolicCost.indexBits D + 40)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 16
        ((SubexpSymbolicCost.fixedKey (a + b)).reverse ++ d.stacks 16) := by
  obtain ⟨ticks, e, hbound, he, hs⟩ := fixedKey_eval d a b ha hb hl hr hw h₀ h₁ h₂ ht
  exact ⟨e, ⟨ticks + 1, by omega, StructuredCalls.compiled_halt_trace he 93 16⟩, hs⟩

end SubexponentialSAT.SubexpDenseKeyProgram

end OAI.Algorithms
