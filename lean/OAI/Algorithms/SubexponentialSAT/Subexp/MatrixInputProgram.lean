import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputAccess

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

open BitProgram StructuredCalls StackRoutines MatrixInputAccess


def sourcePort (second : Bool) : Fin 29 := if second then 24 else 23
def headPort (second : Bool) : Fin 29 := if second then 19 else 17
def slotPort (second : Bool) : Fin 29 := if second then 20 else 18

def WorkReady (a : Data) : Prop :=
  a.stacks 1 = [] ∧ a.stacks 2 = [] ∧ a.stacks 4 = [] ∧ a.stacks 5 = [] ∧
  a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 8 = []

abbrev extract (second : Bool) : Cmd 8 29 :=
  .seq (copy (sourcePort second) 0) (.seq read
    (.seq (copy 1 (headPort second)) (.seq (clear 1)
      (.seq (copy 25 2) (.seq read
        (.seq (copy 1 (slotPort second)) (clear 1)))))))

def extracted (a : Data) (second : Bool) (head slot : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update a.stacks 0 (a.stacks (sourcePort second)))
      (headPort second) head) (slotPort second) slot⟩

theorem extract_eval (a : Data) (second : Bool)
    (head slot width : List Bool) (before after : List (List Bool))
    (hwork : WorkReady a) (h0 : a.stacks 0 = [])
    (hhead : a.stacks (headPort second) = []) (hslot : a.stacks (slotPort second) = [])
    (hsource : a.stacks (sourcePort second) = head ++ before.flatten ++ (slot ++ after.flatten))
    (hw : a.stacks 3 = width) (hi : (a.stacks 25).length = before.length + 1)
    (hh : head.length = width.length) (hs : slot.length = width.length)
    (hb : ∀ row ∈ before, row.length = width.length) :
    Eval (extract second)
      (7 * (a.stacks (sourcePort second)).length +
        (before.length + 1) * (14 * width.length + 17) + 48 * width.length + 58)
      a (extracted a second head slot) := by
  rcases hwork with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  let a1 := copied a (sourcePort second) 0
  let a2 := readResult a1 head
  let a3 := copied a2 1 (headPort second)
  let a4 := cleared a3 1
  let a5 := copied a4 25 2
  let a6 := readResult a5 slot
  let a7 := copied a6 1 (slotPort second)
  have t0 := copy_eval a (sourcePort second) 0
    (by cases second <;> decide) (by cases second <;> decide) (by decide) h8
  have t1 := read_eval a1 [] head (before.flatten ++ (slot ++ after.flatten)) width
    (by simp [a1, copyStacks, h0, hsource, List.append_assoc])
    (by simpa [a1, copied, copyStacks] using hw)
    (by simp [a1, copyStacks, h2]) (by simp) hh
    (by simpa [a1, copied, copyStacks] using h4)
    (by simpa [a1, copied, copyStacks] using h5)
    (by simpa [a1, copied, copyStacks] using h6)
    (by simpa [a1, copied, copyStacks] using h7)
  have t2 := copy_eval a2 1 (headPort second)
    (by cases second <;> decide) (by decide) (by cases second <;> decide)
    (by simp [a2, a1, copyStacks, h8])
  have t3 := clear_eval a3 1
  have t4 := copy_eval a4 25 2 (by decide) (by decide) (by decide)
    (by cases second <;> simp [a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h8])
  have t5 := read_eval a5 (head :: before) slot after.flatten width
    (by cases second <;> simp [a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h0, hsource, List.append_assoc])
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using hw)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using hi)
    (by simpa [hh] using hb) hs
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h4)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h5)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h6)
    (by cases second <;> simpa [a5, a4, a3, a2, a1, cleared, copied, readResult,
      clearStacks, copyStacks, headPort] using h7)
  have t6 := copy_eval a6 1 (slotPort second)
    (by cases second <;> decide) (by decide) (by cases second <;> decide)
    (by cases second <;> simp [a6, a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, h8])
  have t7 := clear_eval a7 1
  have hf : cleared a7 1 = extracted a second head slot := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; cases second <;> fin_cases j <;>
        simp [a7, a6, a5, a4, a3, a2, a1, readRegs]
    · funext j; cases second <;>
        simp only [headPort, slotPort, Bool.false_eq_true, ite_false, ite_true] at hhead hslot <;>
        fin_cases j <;>
        simp [a7, a6, a5, a4, a3, a2, a1,
          clearStacks, copyStacks, sourcePort, headPort, slotPort, h0, h1, h2, hhead, hslot]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq t7))))))
  rw [hf] at ht
  convert ht using 1
  cases second <;>
    simp [a7, a6, a5, a4, a3, a2, a1,
      clearStacks, copyStacks, headPort, slotPort, h1, hh, hs, hi] <;> ring

theorem extracted_workReady (a : Data) (second : Bool) (head slot : List Bool)
    (h : WorkReady a) : WorkReady (extracted a second head slot) := by
  cases second <;> simpa [WorkReady, extracted, headPort, slotPort] using h

abbrev normalize : Cmd 8 29 :=
  .seq (copy 17 1) (.seq replace (.seq (copy 25 2) (.seq replace (clear 1))))

def normalizedBits (common : List Bool) (before after : List (List Bool)) : List Bool :=
  common ++ before.flatten ++ (common ++ after.flatten)

def normalized (a : Data) (before after : List (List Bool)) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 0 (normalizedBits (a.stacks 17) before after)⟩

theorem normalize_eval (a : Data) (head slot width : List Bool)
    (before after : List (List Bool)) (hwork : WorkReady a)
    (hsource : a.stacks 0 = head ++ before.flatten ++ (slot ++ after.flatten))
    (hw : a.stacks 3 = width) (hi : (a.stacks 25).length = before.length + 1)
    (hh : head.length = width.length) (hs : slot.length = width.length)
    (hc : (a.stacks 17).length = width.length)
    (hb : ∀ row ∈ before, row.length = width.length) :
    Eval normalize ((before.length + 1) * (14 * width.length + 17) + 49 * width.length + 55)
      a (normalized a before after) := by
  rcases hwork with ⟨h1, h2, h4, h5, h6, h7, h8⟩
  let a1 := copied a 17 1
  let a2 := replaceResult a1 (a.stacks 17 ++ (before.flatten ++ (slot ++ after.flatten)))
  let a3 := copied a2 25 2
  let a4 := replaceResult a3 ((a.stacks 17 :: before).flatten ++
    (a.stacks 17 ++ after.flatten))
  have t0 := copy_eval a 17 1 (by decide) (by decide) (by decide) h8
  have t1 := replace_eval a1 [] head (a.stacks 17)
    (before.flatten ++ (slot ++ after.flatten)) width
    (by simpa [a1, copied, copyStacks, List.append_assoc] using hsource)
    (by simp [a1, copyStacks, h1])
    (by simpa [a1, copied, copyStacks] using hw)
    (by simp [a1, copyStacks, h2]) (by simp) hh hc
    (by simpa [a1, copied, copyStacks] using h4)
    (by simpa [a1, copied, copyStacks] using h5)
    (by simpa [a1, copied, copyStacks] using h6)
    (by simpa [a1, copied, copyStacks] using h7)
  have t2 := copy_eval a2 25 2 (by decide) (by decide) (by decide)
    (by simp [a2, a1, copyStacks, h8])
  have t3 := replace_eval a3 (a.stacks 17 :: before) slot (a.stacks 17) after.flatten width
    (by simp [a3, a2, a1, copyStacks, List.append_assoc])
    (by simp [a3, a2, a1, copyStacks, h1])
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using hw)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using hi)
    (by simpa [hc] using hb) hs hc
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h4)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h5)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h6)
    (by simpa [a3, a2, a1, copied, replaceResult, copyStacks] using h7)
  have t4 := clear_eval a4 1
  have hf : cleared a4 1 = normalized a before after := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, readRegs]
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, clearStacks, copyStacks, normalizedBits, h1, h2,
        List.append_assoc]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq t4)))
  rw [hf] at ht
  convert ht using 1
  simp [a4, a3, a2, a1, copyStacks, h1, hc, hi]
  ring

theorem normalized_workReady (a : Data) (before after : List (List Bool))
    (h : WorkReady a) : WorkReady (normalized a before after) := by
  simpa [WorkReady, normalized] using h

abbrev command : Cmd 8 29 :=
  .seq (copy 26 3) (.seq (extract false) (.seq normalize
    (.seq (copy 0 28) (.seq (clear 0) (.seq (extract true)
      (.seq normalize (.seq equality (clear 3))))))))

def program := compiled command 23 17

theorem control_size : StructuredCalls.size command + 1 = 488 := rfl

def array (head slot : List Bool) (before after : List (List Bool)) : List Bool :=
  head ++ before.flatten ++ (slot ++ after.flatten)

def inputState (left right index width colors positions : List Bool)
    (regs : Fin 8 → Bool) : Data :=
  ⟨regs, fun j => if j = 21 then colors else if j = 22 then positions
    else if j = 23 then left else if j = 24 then right else if j = 25 then index
    else if j = 26 then width else []⟩

def outputState (left right index width colors positions : List Bool)
    (headU slotU headY slotY : List Bool) (answer : Bool) (regs : Fin 8 → Bool) : Data :=
  ⟨fun j => if j = 7 then answer else if j.val < 5 then false else regs j,
    fun j => if j = 17 then headU else if j = 18 then slotU else if j = 19 then headY
      else if j = 20 then slotY else (inputState left right index width colors positions regs).stacks j⟩

theorem reset_compared_regs (regs : Fin 8 → Bool) (answer : Bool) :
    readRegs (fun j => if j = 7 then answer else if j.val < 5 then false
      else readRegs regs 0 1 none j) 0 1 none =
      (fun j => if j = 7 then answer else if j.val < 5 then false else regs j) := by
  funext j
  by_cases h0 : j = 0
  · subst j; rfl
  by_cases h1 : j = 1
  · subst j; rfl
  simp [readRegs, h0, h1]

def cost (left right index width : List Bool) : ℕ :=
  18 * (left.length + right.length) +
    4 * index.length * (14 * width.length + 17) + 203 * width.length + 265

theorem program_runsIn (headU slotU headY slotY index width colors positions : List Bool)
    (beforeU afterU beforeY afterY : List (List Bool)) (regs : Fin 8 → Bool)
    (hiU : index.length = beforeU.length + 1) (hiY : index.length = beforeY.length + 1)
    (hhU : headU.length = width.length) (hsU : slotU.length = width.length)
    (hhY : headY.length = width.length) (hsY : slotY.length = width.length)
    (hbU : ∀ row ∈ beforeU, row.length = width.length)
    (hbY : ∀ row ∈ beforeY, row.length = width.length) :
    RunsIn program
      (cost (array headU slotU beforeU afterU) (array headY slotY beforeY afterY) index width)
      ((inputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions regs).withPC (some program.entry))
      ((outputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions headU slotU headY slotY
        (decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY))
        regs).withPC none) := by
  let a := inputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
    index width colors positions regs
  let a1 := copied a 26 3
  let a2 := extracted a1 false headU slotU
  let a3 := normalized a2 beforeU afterU
  let a4 := copied a3 0 28
  let a5 := cleared a4 0
  let a6 := extracted a5 true headY slotY
  let a7 := normalized a6 beforeY afterY
  let a8 := compared a7 (decide (a7.stacks 0 = a7.stacks 28))
  have t0 := copy_eval a 26 3 (by decide) (by decide) (by decide) (by simp [a, inputState])
  have hw1 : WorkReady a1 := by simp [a1, a, copyStacks, inputState, WorkReady]
  have t1 := extract_eval a1 false headU slotU width beforeU afterU hw1
    (by simp [a1, a, copyStacks, inputState])
    (by simp [a1, a, copyStacks, inputState, headPort])
    (by simp [a1, a, copyStacks, inputState, slotPort])
    (by simp [a1, a, copyStacks, inputState, sourcePort, array])
    (by simp [a1, a, copyStacks, inputState])
    (by simpa [a1, a, copied, copyStacks, inputState] using hiU) hhU hsU hbU
  have hw2 : WorkReady a2 := extracted_workReady _ _ _ _ hw1
  have t2 := normalize_eval a2 headU slotU width beforeU afterU hw2
    (by simp [a2, a1, a, extracted, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a2, a1, a, extracted, copyStacks, inputState, headPort, slotPort])
    (by simpa [a2, a1, a, extracted, copied, copyStacks, inputState, headPort, slotPort] using hiU)
    hhU hsU (by simpa [a2, extracted, headPort, slotPort] using hhU) hbU
  have hw3 : WorkReady a3 := normalized_workReady _ _ _ hw2
  have t3 := copy_eval a3 0 28 (by decide) (by decide) (by decide) hw3.2.2.2.2.2.2
  have t4 := clear_eval a4 0
  have hw5 : WorkReady a5 := by simpa [a5, a4, cleared, copied, clearStacks, copyStacks, WorkReady] using hw3
  have t5 := extract_eval a5 true headY slotY width beforeY afterY hw5
    (by simp [a5, clearStacks])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simpa [a5, a4, a3, a2, a1, a, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort] using hiY) hhY hsY hbY
  have hw6 : WorkReady a6 := extracted_workReady _ _ _ _ hw5
  have t6 := normalize_eval a6 headY slotY width beforeY afterY hw6
    (by simp [a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, sourcePort, headPort, slotPort, array])
    (by simp [a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
    (by simpa [a6, a5, a4, a3, a2, a1, a, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort] using hiY)
    hhY hsY
    (by simpa [a6, a5, a4, a3, a2, cleared, copied, normalized, extracted,
      clearStacks, copyStacks, headPort, slotPort] using hhU) hbY
  obtain ⟨ne, hne, te⟩ := equality_eval a7
    (by simp [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort])
  have t8 := clear_eval a8 3
  have ha7left : a7.stacks 0 = normalizedBits headU beforeY afterY := by
    simp [a7, a6, a5, a4, a3, a2, normalized, extracted,
      clearStacks, copyStacks, headPort, slotPort]
  have ha7right : a7.stacks 28 = normalizedBits headU beforeU afterU := by
    simp [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      clearStacks, copyStacks, inputState, headPort, slotPort]
  have ha7regs : a7.regs = readRegs regs 0 1 none := by
    simp only [a7, a6, a5, a4, a3, a2, a1, a, normalized, extracted,
      inputState, readRegs_reset]
  have hanswer :
      decide (normalizedBits headU beforeY afterY = normalizedBits headU beforeU afterU) =
      decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY) :=
    decide_eq_decide.mpr eq_comm
  have hf : cleared a8 3 =
      outputState (array headU slotU beforeU afterU) (array headY slotY beforeY afterY)
        index width colors positions headU slotU headY slotY
        (decide (normalizedBits headU beforeU afterU = normalizedBits headU beforeY afterY)) regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · change readRegs (fun k => if k = 7 then decide (a7.stacks 0 = a7.stacks 28)
        else if k.val < 5 then false else a7.regs k) 0 1 none = _
      rw [ha7left, ha7right, ha7regs, hanswer]
      exact reset_compared_regs regs _
    · funext j; fin_cases j <;>
        simp [a8, a7, a6, a5, a4, a3, a2, a1, a, normalized,
          extracted, inputState, copyStacks, clearStacks, sourcePort, headPort, slotPort]
  have ht := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (te.seq t8)))))))
  rw [hf] at ht
  refine ⟨_, ?_, compiled_halt_trace ht 23 17⟩
  dsimp [cost]
  simp only [a8, a7, a6, a5, a4, a3, a2, a1, a, normalized,
    extracted, inputState, sourcePort, headPort, slotPort, copyStacks, clearStacks,
    Function.update_self, ↓reduceIte] at hne ⊢
  simp [normalizedBits, array, hhU, hsU, hhY, hsY, List.length_append] at hne ⊢
  rw [← hiU, ← hiY]
  nlinarith only [hne]

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
