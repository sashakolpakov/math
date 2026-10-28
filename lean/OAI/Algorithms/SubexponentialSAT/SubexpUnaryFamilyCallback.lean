import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFactorTable
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! The closed callback mapping one chunk-width record to its actual unary
validity table.  The scope stream on stack 19 is framed throughout. -/

namespace SubexponentialSAT.SubexpUnaryFamilyCallback

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 16 20

def bankReg (i : Fin 8) : Fin 16 := i.castAdd 8
def bankStack (i : Fin 16) : Fin 20 := ⟨i.val + 3, by omega⟩

theorem bankReg_injective : Function.Injective bankReg := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [bankStack] at hv
  omega

@[simp] theorem bankStack_ne_zero (i : Fin 16) : bankStack i ≠ 0 := by
  intro h; have hv := congrArg Fin.val h; simp [bankStack] at hv

@[simp] theorem bankStack_ne_one (i : Fin 16) : bankStack i ≠ 1 := by
  intro h; have hv := congrArg Fin.val h; simp [bankStack] at hv

@[simp] theorem bankStack_ne_two (i : Fin 16) : bankStack i ≠ 2 := by
  intro h; have hv := congrArg Fin.val h; simp [bankStack] at hv

@[simp] theorem bankStack_ne_scope (i : Fin 16) : bankStack i ≠ 19 := by
  intro h; have hv := congrArg Fin.val h; simp [bankStack] at hv; omega

@[simp] theorem bankStack_eq (i j : Fin 16) : bankStack i = bankStack j ↔ i = j :=
  bankStack_injective.eq_iff

def Clean (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks (bankStack i) = []

abbrev coreCall : Cmd 16 20 := .call (ProgramLinking.liftProgram
  SubexpUnaryFactorTable.program bankReg bankStack)

private theorem coreReady_clear (a : SubexpUnaryRowProgram.Data)
    (ha : SubexpUnaryFactorTable.Ready a) (i : Fin 16)
    (h13 : i ≠ 13) (h14 : i ≠ 14) (h15 : i ≠ 15) : a.stacks i = [] := by
  rcases ha with ⟨hc, h10, h11, h12⟩
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc 3
  · exact hc 4
  · exact hc 5
  · exact hc 6
  · exact hc 7
  · exact hc 8
  · exact hc 9
  · exact h10
  · exact h11
  · exact h12
  · exact (h13 rfl).elim
  · exact (h14 rfl).elim
  · exact (h15 rfl).elim

theorem coreCall_eval (modulus width : List Bool) (d : Data)
    (hp : d.stacks 16 = modulus) (hw : d.stacks 17 = width)
    (hwidth : width.length ≤ modulus.length)
    (hc : ∀ i : Fin 16, i ≠ 13 → i ≠ 14 → i ≠ 15 → d.stacks (bankStack i) = []) :
    ∃ n ≤ 200 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2, ∃ e : Data,
      Eval coreCall n d e ∧
      e.stacks = Function.update d.stacks 18
        (SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus) ++ d.stacks 18) := by
  let a := projectState bankReg bankStack d
  have ha : SubexpUnaryFactorTable.Ready a := by
    refine ⟨?_, hc 10 (by decide) (by decide) (by decide),
      hc 11 (by decide) (by decide) (by decide), hc 12 (by decide) (by decide) (by decide)⟩
    intro i
    have h13 : i.castAdd 6 ≠ (13 : Fin 16) := by
      intro h; have hv := congrArg Fin.val h; change i.val = 13 at hv; omega
    have h14 : i.castAdd 6 ≠ (14 : Fin 16) := by
      intro h; have hv := congrArg Fin.val h; change i.val = 14 at hv; omega
    have h15 : i.castAdd 6 ≠ (15 : Fin 16) := by
      intro h; have hv := congrArg Fin.val h; change i.val = 15 at hv; omega
    exact hc _ h13 h14 h15
  obtain ⟨b, hb, hb13, hb14, hb15, n, hn, ht⟩ :=
    SubexpUnaryFactorTable.program_runsIn modulus width a hp hw hwidth ha
  let e := embedState bankReg bankStack d b
  have he := eval_call_from_state SubexpUnaryFactorTable.program bankReg bankStack d
    bankReg_injective bankStack_injective ht
  have hlocal : b.stacks = Function.update a.stacks 15
      (SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus) ++ a.stacks 15) := by
    funext i
    by_cases h15 : i = 15
    · subst i; simpa using hb15
    rw [Function.update_of_ne h15]
    by_cases h13 : i = 13
    · subst i
      change b.stacks 13 = d.stacks 16
      exact hb13.trans hp.symm
    by_cases h14 : i = 14
    · subst i
      change b.stacks 14 = d.stacks 17
      exact hb14.trans hw.symm
    rw [coreReady_clear b hb i h13 h14 h15, coreReady_clear a ha i h13 h14 h15]
  refine ⟨n, hn, e, he, ?_⟩
  change Function.extend bankStack b.stacks d.stacks = _
  rw [hlocal, ProgramLinking.extend_update bankStack_injective]
  have hproject : Function.extend bankStack a.stacks d.stacks = d.stacks := by
    exact congrArg StructuredProgram.State.stacks
      (embedState_project bankReg bankStack d bankReg_injective bankStack_injective)
  rw [hproject]
  rfl

abbrev transfer (src dst : Fin 20) : Cmd 16 20 := .call (transferProgram src dst 0 1)
def transferred (src dst : Fin 20) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 20) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

abbrev clear (src : Fin 20) : Cmd 16 20 := .call (clearProgram src 0 1)
def cleared (src : Fin 20) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 20) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

def emitReg (i : Fin 3) : Fin 16 := ⟨i.val + 13, by omega⟩
def emitStack : Fin 4 → Fin 20 := ![0, 3, 2, 1]

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [emitReg] at hv
  omega

theorem emitStack_injective : Function.Injective emitStack := by decide

abbrev emitCall : Cmd 16 20 := liftCommand SubexpNormalizeProgram.emitEveryRecord
  0 2 emitReg emitStack

theorem emitCall_eval (bits : List Bool) (d : Data) (hp : d.stacks 1 = bits.reverse) :
    ∃ e : Data, Eval emitCall (5 * bits.length + 13) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame bits ++ d.stacks 2) ∧
      (∀ i : Fin 20, 3 ≤ i.val → e.stacks i = d.stacks i) ∧
      e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  let a := SubexpNormalizeProgram.filterState (d.regs 13) (d.regs 14) (d.regs 15)
    (d.stacks 0) (d.stacks 3) (d.stacks 2) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 3) (true :: (Encoding.frame bits ++ d.stacks 2)) []
  have ha : a = projectState emitReg emitStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ emitStack, SubexpPostfixControl.quadruple, hp]
  have he := eval_liftCommand (SubexpNormalizeProgram.emitEveryRecord_eval bits
    (d.stacks 0) (d.stacks 3) (d.stacks 2) (d.regs 13) (d.regs 14) (d.regs 15))
    0 2 emitReg emitStack d emitReg_injective emitStack_injective
  change Eval emitCall (5 * bits.length + 12 + 1) (embedState emitReg emitStack d a)
    (embedState emitReg emitStack d b) at he
  rw [ha, embedState_project _ _ _ emitReg_injective emitStack_injective] at he
  let e := embedState emitReg emitStack d b
  have hs (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hr (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, by simpa only [Nat.add_assoc] using he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs 0
  · exact hs 3
  · exact hs 2
  · intro i hi
    by_cases h3 : i = 3
    · subst i; exact hs 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [emitStack] at hj <;> subst i <;> simp_all
  · exact hr 0
  · exact hr 1
  · exact hr 2

abbrev callback : Cmd 16 20 :=
  .seq (transfer 1 17) (.seq coreCall
    (.seq (clear 17) (.seq (transfer 18 1) emitCall)))

theorem callback_eval (width modulus : List Bool) (d : Data)
    (hq : d.stacks 1 = width.reverse) (hp : d.stacks 16 = modulus)
    (hw : width.length ≤ modulus.length) (hc : Clean d) :
    ∃ n ≤ 240 * (CounterPrograms.value modulus + modulus.length + 1) ^ 2, ∃ e : Data,
      Eval callback n d e ∧ Clean e ∧ e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame
        (SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus)) ++ d.stacks 2) ∧
      e.stacks 16 = modulus ∧ e.stacks 19 = d.stacks 19 ∧
      e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  let a := transferred 1 17 d
  have hd17 : d.stacks 17 = [] := hc 14 (by decide)
  have hd18 : d.stacks 18 = [] := hc 15 (by decide)
  have ha17 : a.stacks 17 = width := by simp [a, transferred, transferStacks, hq, hd17]
  have ha16 : a.stacks 16 = modulus := by simpa [a, transferred, transferStacks] using hp
  have haw : ∀ i : Fin 16, i ≠ 13 → i ≠ 14 → i ≠ 15 → a.stacks (bankStack i) = [] := by
    intro i hi13 hi14 hi15
    have hi17 : bankStack i ≠ (17 : Fin 20) := fun h => hi14 (bankStack_injective h)
    simp [a, transferred, transferStacks, hi17, hc i hi13]
  obtain ⟨m, hm, e, he, hew⟩ := coreCall_eval modulus width a ha16 ha17 hw haw
  have he17 : e.stacks 17 = width := by simp [hew, ha17]
  have he18 : e.stacks 18 = SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus) := by
    simp [hew, a, transferred, transferStacks, hd18]
  let b := cleared 17 e
  let c := transferred 18 1 b
  have hc1 : c.stacks 1 =
      (SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus)).reverse := by
    simp [c, b, transferred, cleared, transferStacks, clearStacks, hew, a, hd18]
  have hcc : Clean c := by
    intro i hi
    by_cases h14 : i = 14
    · subst i
      change c.stacks 17 = []
      simp [c, b, transferred, cleared, transferStacks, clearStacks]
    by_cases h15 : i = 15
    · subst i
      change c.stacks 18 = []
      simp [c, b, transferred, cleared, transferStacks, clearStacks]
    have hi17 : bankStack i ≠ (17 : Fin 20) := fun h => h14 (bankStack_injective h)
    have hi18 : bankStack i ≠ (18 : Fin 20) := fun h => h15 (bankStack_injective h)
    simp [c, b, transferred, cleared, transferStacks, clearStacks, hew, a, hi17, hi18, hc i hi]
  obtain ⟨f, hf, hf0, hf1, hf2, hfw, hf13, hf14, hf15⟩ :=
    emitCall_eval _ c hc1
  let steps := (3 * (d.stacks 1).length + 3) +
    (m + ((2 * (e.stacks 17).length + 3) +
      ((3 * (b.stacks 18).length + 3) +
        (5 * (SubexpUnaryFactorTable.table width.length (CounterPrograms.value modulus)).length + 13))))
  refine ⟨steps, ?_, f, ?_, ?_, ?_, hf1, ?_, ?_, ?_, hf13, hf14, hf15⟩
  · dsimp [steps]
    simp only [hq, List.length_reverse, he17, b, cleared, clearStacks,
      Function.update_of_ne (by decide : (18 : Fin 20) ≠ 17), he18,
      SubexpUnaryFactorTable.table_length]
    let K := CounterPrograms.value modulus + modulus.length + 1
    have hmK : m ≤ 200 * K ^ 2 := by simpa [K] using hm
    have hK : 1 ≤ K := by omega
    have hsq : K ≤ K ^ 2 := by nlinarith
    have hk : CounterPrograms.value modulus ≤ K := by omega
    have hwK : width.length ≤ K := hw.trans (by omega)
    have hextra : 5 * width.length + 8 * CounterPrograms.value modulus + 22 ≤ 40 * K ^ 2 := by
      calc
        5 * width.length + 8 * CounterPrograms.value modulus + 22 ≤ 40 * K := by omega
        _ ≤ 40 * K ^ 2 := Nat.mul_le_mul_left 40 hsq
    calc
      _ = m + (5 * width.length + 8 * CounterPrograms.value modulus + 22) := by ring
      _ ≤ 200 * K ^ 2 +
          (5 * width.length + 8 * CounterPrograms.value modulus + 22) :=
        Nat.add_le_add_right hmK _
      _ ≤ 200 * K ^ 2 + 40 * K ^ 2 := Nat.add_le_add_left hextra _
      _ = 240 * K ^ 2 := by ring
  · exact (transfer_eval 1 17 (by decide) d).seq
      (he.seq ((clear_eval 17 e).seq ((transfer_eval 18 1 (by decide) b).seq hf)))
  · intro i hi
    exact (hfw (bankStack i) (by simp [bankStack])).trans (hcc i hi)
  · simpa [c, b, transferred, cleared, transferStacks, clearStacks, hew, a] using hf0
  · simpa [c, b, transferred, cleared, transferStacks, clearStacks, hew, a] using hf2
  · simpa [c, b, transferred, cleared, transferStacks, clearStacks, hew, a, hp] using hfw 16 (by decide)
  · simpa [c, b, transferred, cleared, transferStacks, clearStacks, hew, a] using hfw 19 (by decide)

end SubexponentialSAT.SubexpUnaryFamilyCallback

end OAI.Algorithms
