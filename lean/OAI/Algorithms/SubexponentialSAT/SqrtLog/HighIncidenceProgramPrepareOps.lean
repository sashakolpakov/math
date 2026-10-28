import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMassPreserve
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramCutoff

namespace OAI.Algorithms

/-! Fixed ports for the physical high-incidence prefix. Each operation below
is a genuine call to an already verified finite program. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 10 32
abbrev Code := Cmd 10 32
def reg8 : Fin 8 → Fin 10 := Fin.castAdd 2
def reg3 : Fin 3 → Fin 10 := Fin.castAdd 7
theorem reg8_inj : Function.Injective reg8 := Fin.castAdd_injective _ _
theorem reg3_inj : Function.Injective reg3 := Fin.castAdd_injective _ _

def countPorts : Fin 15 → Fin 32 := ![24, 0, 1, 3, 4, 21, 5, 6, 7, 8, 9, 10, 11, 12, 22]
def massPorts : Fin 5 → Fin 32 := ![0, 21, 18, 22, 23]
def binaryPorts : Fin 13 → Fin 32 := ![24, 18, 19, 25, 21, 22, 3, 4, 5, 6, 7, 8, 9]
def cutoffPorts : Fin 12 → Fin 32 := ![19, 17, 16, 24, 25, 20, 26, 27, 28, 29, 30, 31]
def unaryPorts : Fin 14 → Fin 32 := ![20, 13, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 22, 23]
def fuelPorts : Fin 14 → Fin 32 := ![16, 15, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 22, 23]
theorem countPorts_inj : Function.Injective countPorts := by decide
theorem massPorts_inj : Function.Injective massPorts := by decide
theorem binaryPorts_inj : Function.Injective binaryPorts := by decide
theorem cutoffPorts_inj : Function.Injective cutoffPorts := by decide
theorem unaryPorts_inj : Function.Injective unaryPorts := by decide
theorem fuelPorts_inj : Function.Injective fuelPorts := by decide

def countCall : Code := liftCommand SubexpScopeCountSetup.countCommand 1 2 reg8 countPorts
def massCall : Code := liftCommand MassPreserve.command 0 2 reg8 massPorts
def binaryCall : Code := liftCommand SubexpFactorCountSetup.countCommand 1 2 reg8 binaryPorts
def cutoffCall : Code := liftCommand Cutoff.command 0 5 reg8 cutoffPorts
def unaryCall : Code := liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 unaryPorts
def fuelCall : Code := liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 fuelPorts
def bump : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 13 0)))

theorem count_eval (d : Data) (records : List (List Bool))
    (h0 : d.stacks 0 = Encoding.encodeList id records)
    (h1 : d.stacks 1 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = []) :
    ∃ rf, Eval countCall (SubexpScopeCountSetup.countBudget records + 1) d
      ⟨rf, Function.update d.stacks 1 (List.replicate records.length true)⟩ := by
  obtain ⟨rf, he⟩ := SubexpScopeCountSetup.count_eval records (projectState reg8 countPorts d)
    h0 h1 h21 h22
  exact lift_update _ 1 2 reg8 countPorts d reg8_inj countPorts_inj 2 _ rf _ he

theorem mass_eval (d : Data) (scopes : List (List ℕ))
    (h0 : d.stacks 0 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (h18 : d.stacks 18 = []) (h21 : d.stacks 21 = [])
    (h22 : d.stacks 22 = []) (h23 : d.stacks 23 = []) :
    ∃ time rf, Eval massCall time d
      ⟨rf, Function.update d.stacks 18 (List.replicate ((scopes.map List.length).sum) true)⟩ ∧
      time ≤ MassPreserve.bound (SubexpIncidenceSlotProgram.scopeBits scopes) := by
  let a := projectState reg8 massPorts d
  have ha : a = MassPreserve.state a.regs (SubexpIncidenceSlotProgram.scopeBits scopes) [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;> simp [ massPorts, h0, h18, h21, h22, h23]
  obtain ⟨time, rf, he, ht⟩ := MassPreserve.command_eval a.regs scopes
  have hs : (MassPreserve.state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
      (List.replicate ((scopes.map List.length).sum) true)).stacks =
      Function.update a.stacks 2 (List.replicate ((scopes.map List.length).sum) true) := by
    rw [ha]
    funext i; fin_cases i <;> rfl
  rw [← ha] at he
  have hb : MassPreserve.state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
      (List.replicate ((scopes.map List.length).sum) true) =
      (⟨rf, Function.update a.stacks 2 (List.replicate ((scopes.map List.length).sum) true)⟩ : MassPreserve.Data) :=
    congrArg (StructuredProgram.State.mk rf) hs
  rw [hb] at he
  obtain ⟨r, hr⟩ := lift_update _ 0 2 reg8 massPorts d reg8_inj massPorts_inj 2 _ rf time he
  exact ⟨time + 1, r, hr, ht⟩

theorem binary_eval (d : Data) (h19 : d.stacks 19 = [])
    (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = []) :
    ∃ time rf bits, Eval binaryCall time d ⟨rf, Function.update d.stacks 19 bits⟩ ∧
      time ≤ SubexpFactorCountSetup.countBudget (d.stacks 18).length + 1 ∧
      BinaryArithmetic.toNat bits = (d.stacks 18).length ∧ bits.length ≤ (d.stacks 18).length := by
  obtain ⟨time, ht, rf, bits, he, hv, hl⟩ :=
    SubexpFactorCountSetup.count_eval (projectState reg8 binaryPorts d) h19 h21 h22
  obtain ⟨r, hr⟩ := lift_update _ 1 2 reg8 binaryPorts d reg8_inj binaryPorts_inj 2 bits rf time he
  exact ⟨time + 1, r, bits, hr, Nat.add_le_add_right ht 1, hv, hl⟩

theorem unary_eval (ports : Fin 14 → Fin 32) (hi : Function.Injective ports)
    (d : Data) (h1 : d.stacks (ports 1) = [])
    (h11 : d.stacks (ports 11) = []) (h12 : d.stacks (ports 12) = [])
    (h13 : d.stacks (ports 13) = []) :
    ∃ time rf, Eval (liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 ports)
      time d ⟨rf, Function.update d.stacks (ports 1)
        (List.replicate (BinaryArithmetic.toNat (d.stacks (ports 0))) true)⟩ ∧
      time ≤ SubexpClauseMastersProgram.unaryCopyBound (d.stacks (ports 0)) + 1 := by
  obtain ⟨time, ht, he⟩ := SubexpClauseMastersProgram.unaryCopy_eval 0 1
    (projectState reg3 ports d) (by decide) (by decide) (by decide) (by decide)
    h1 h11 h12 h13
  simp only [SubexpClauseMastersProgram.write, SubexpClauseMastersProgram.unary,
    CounterPrograms.value_eq_toNat] at he
  obtain ⟨rf, hr⟩ := lift_update _ 0 1 reg3 ports d reg3_inj hi 1 _ _ time he
  exact ⟨time + 1, rf, hr, Nat.add_le_add_right ht 1⟩

theorem bump_eval (d : Data) :
    Eval bump 2 d ⟨Function.update d.regs 0 true,
      Function.update d.stacks 13 (true :: d.stacks 13)⟩ :=
  (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

theorem cutoff_eval (d : Data) (hn : 0 < BinaryArithmetic.toNat (d.stacks 16))
    (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → d.stacks (cutoffPorts i) = []) :
    ∃ time b, Eval cutoffCall time d b ∧
      time ≤ Cutoff.bound (d.stacks 19) (d.stacks 17) (d.stacks 16) ∧
      BinaryArithmetic.toNat (b.stacks 20) = (BinaryArithmetic.toNat (d.stacks 19) * BinaryArithmetic.toNat (d.stacks 17)) ⌈/⌉ BinaryArithmetic.toNat (d.stacks 16) ∧
      (b.stacks 20).length ≤ (d.stacks 19).length + (d.stacks 17).length + 2 ∧
      (∀ i : Fin 32, i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
        i = 21 ∨ i = 22 ∨ i = 23 → b.stacks i = d.stacks i) := by
  let a := projectState reg8 cutoffPorts d
  have ha : a = Cutoff.state a.regs (d.stacks 19) (d.stacks 17) (d.stacks 16) := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i
    fin_cases i <;> first | rfl | exact hwork _ (by decide) (by decide) (by decide)
  obtain ⟨time, out, he, ht, hv, hl, h0, h1, h2⟩ :=
    Cutoff.command_eval a.regs (d.stacks 19) (d.stacks 17) (d.stacks 16) hn
  rw [← ha] at he
  let b := embedState reg8 cutoffPorts d out
  have hb := eval_liftCommand_from_state Cutoff.command 0 5 reg8 cutoffPorts d
    reg8_inj cutoffPorts_inj he
  have hs (i : Fin 12) : b.stacks (cutoffPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ cutoffPorts_inj i
  refine ⟨time + 1, b, hb, ht, (congrArg BinaryArithmetic.toNat (hs 5)).trans hv, ?_, ?_⟩
  · change (b.stacks (cutoffPorts 5)).length ≤
      (d.stacks 19).length + (d.stacks 17).length + 2
    rw [hs 5]
    exact hl
  · intro i hi
    by_cases h16 : i = 16
    · subst i; exact (hs 2).trans h2
    by_cases h17 : i = 17
    · subst i; exact (hs 1).trans h1
    by_cases h19 : i = 19
    · subst i; exact (hs 0).trans h0
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    have h16' : i.val ≠ 16 := fun h => h16 (Fin.ext h)
    have h17' : i.val ≠ 17 := fun h => h17 (Fin.ext h)
    have h19' : i.val ≠ 19 := fun h => h19 (Fin.ext h)
    have hi' : i.val < 16 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨
        i.val = 21 ∨ i.val = 22 ∨ i.val = 23 := by simpa [Fin.ext_iff] using hi
    fin_cases j <;> norm_num [cutoffPorts] at hjv <;> omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
