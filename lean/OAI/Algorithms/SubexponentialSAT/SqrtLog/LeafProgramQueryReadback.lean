import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramReadbackModel
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

abbrev Data := State 19 330

def regMap (i : Fin 8) : Fin 19 := i.castAdd 11
def stackMap : Fin 8 → Fin 330 := ![261, 325, 326, 327, 328, 194, 329, 202]

theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 8 11

theorem stackMap_injective : Function.Injective stackMap := by decide

def project (a : Data) : State 8 8 := ⟨a.regs ∘ regMap, a.stacks ∘ stackMap⟩
noncomputable def install (a : Data) (b : State 8 8) : Data := embedState regMap stackMap a b

theorem install_project (a : Data) : install a (project a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, regMap j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_register regMap stackMap a (project a) regMap_injective j
    · exact embedState_register_frame regMap stackMap a (project a) i h
  · funext i
    by_cases h : ∃ j, stackMap j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_stack regMap stackMap a (project a) stackMap_injective j
    · exact embedState_stack_frame regMap stackMap a (project a) i h

abbrev readCommand : Cmd 19 330 :=
  .call (ProgramLinking.liftProgram Readback.countProgram regMap stackMap)

abbrev moveCommand : Cmd 19 330 :=
  .seq (.call (StackRoutines.transferProgram 261 324 0 1))
    (.call (StackRoutines.transferProgram 324 323 0 1))

def afterMove (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 324 323 (StackRoutines.transferStacks 261 324 a.stacks)⟩

theorem move_eval (a : Data) (ha : a.stacks 324 = []) :
    Eval moveCommand (6 * (a.stacks 261).length + 6) a (afterMove a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 261 324 a.stacks⟩
  have h1 := ListRegisterProgram.transfer_run (261 : Fin 330) 324 (0 : Fin 19) 1
    (by decide) (by decide) a.regs a.stacks
  have h2 := ListRegisterProgram.transfer_run (324 : Fin 330) 323 (0 : Fin 19) 1
    (by decide) (by decide) (readRegs a.regs 0 1 none)
    (StackRoutines.transferStacks 261 324 a.stacks)
  have e1 : Eval (.call (StackRoutines.transferProgram 261 324 0 1))
      (3 * (a.stacks 261).length + 3) a mid := Eval.call _ h1
  have e2 : Eval (.call (StackRoutines.transferProgram 324 323 0 1))
      (3 * (mid.stacks 324).length + 3) mid
      ⟨readRegs mid.regs 0 1 none, StackRoutines.transferStacks 324 323 mid.stacks⟩ :=
    Eval.call _ h2
  have he := Eval.seq e1 e2
  convert he using 1 <;>
    simp [ afterMove, mid, StackRoutines.transferStacks,
      ha, StackRoutines.readRegs_reset] ; omega

@[simp] theorem afterMove_output (a : Data) (hs : a.stacks 323 = []) (ht : a.stacks 324 = []) :
    (afterMove a).stacks 323 = a.stacks 261 := by
  simp [afterMove, StackRoutines.transferStacks, hs, ht]

@[simp] theorem afterMove_scratch (a : Data) : (afterMove a).stacks 324 = [] := by
  simp [afterMove, StackRoutines.transferStacks]

theorem afterMove_frame (a : Data) (i : Fin 330) (h1 : i ≠ 261) (h2 : i ≠ 323) (h3 : i ≠ 324) :
    (afterMove a).stacks i = a.stacks i := by
  simp [afterMove, StackRoutines.transferStacks, h1, h2, h3]

abbrev command : Cmd 19 330 := .seq readCommand moveCommand
def program := compiled command 261 323

private theorem install_stack_frame (a : Data) (b : State 8 8) (i : Fin 330)
    (hi : i ∉ ([261, 325, 326, 327, 328, 194, 329, 202] : List (Fin 330))) :
    (install a b).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  apply hi
  rw [← hj]
  fin_cases j <;> simp [stackMap]

/-- Full primitive adapter; the count value follows from the actual model's
constant-coordinate theorem, after a measured modular reduction. -/
theorem run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (z : model.O t))
    (a : Data) (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = SubexpLiftRing.baseWidth 3 t)
    (ready : project a = start regs modulus width (RingProgram.flat x))
    (hs : a.stacks 323 = []) (ha : a.stacks 324 = []) :
    ∃ n b, n ≤ budget (SubexpLiftRing.baseWidth 3 t) modulus (RingProgram.flat x) +
        6 * (modulus.length + SubexpLiftRing.baseWidth 3 t) + 6 ∧
      Eval command n a b ∧ BinaryArithmetic.toNat (b.stacks 323) = z ∧
      b.stacks 324 = [] ∧ b.stacks 320 = a.stacks 320 ∧ b.stacks 322 = a.stacks 322 ∧
      ∃ finalRegs word, word.length = modulus.length + SubexpLiftRing.baseWidth 3 t ∧
        b = afterMove (install a ⟨finalRegs, store word modulus [] width⟩) := by
  obtain ⟨finalRegs, word, hv, hlen, n, hn, htrace⟩ :=
    Readback.model_countProgram_run t ht hd model M cache x z hz hx regs modulus width hm hw
  let c : State 8 8 := ⟨finalRegs, store word modulus [] width⟩
  let b := install a c
  change Trace Readback.countProgram n
    ((start regs modulus width (RingProgram.flat x)).withPC (some Readback.countProgram.entry))
    (c.withPC none) at htrace
  have hread : Eval readCommand n a b := by
    have hh := eval_call_lifted Readback.countProgram regMap stackMap a
      regMap_injective stackMap_injective (a := start regs modulus width (RingProgram.flat x))
      (b := c) htrace
    have he : install a (start regs modulus width (RingProgram.flat x)) = a := by
      rw [← ready, install_project]
    change Eval readCommand n (install a (start regs modulus width (RingProgram.flat x))) b at hh
    rw [he] at hh
    exact hh
  have hs' : b.stacks 323 = [] := by
    rw [install_stack_frame _ _ _ (by decide)]
    exact hs
  have ha' : b.stacks 324 = [] := by
    rw [install_stack_frame _ _ _ (by decide)]
    exact ha
  have hword : b.stacks 261 = word :=
    embedState_stack regMap stackMap a c stackMap_injective 0
  refine ⟨n + (6 * (b.stacks 261).length + 6), afterMove b, ?_,
    Eval.seq hread (move_eval b ha'), ?_, afterMove_scratch b, ?_, ?_, ⟨finalRegs, word, hlen, rfl⟩⟩
  · rw [hword]
    omega
  · rw [afterMove_output _ hs' ha', hword]
    exact hv
  · rw [afterMove_frame _ _ (by decide) (by decide) (by decide),
      install_stack_frame _ _ _ (by decide)]
  · rw [afterMove_frame _ _ (by decide) (by decide) (by decide),
      install_stack_frame _ _ _ (by decide)]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
