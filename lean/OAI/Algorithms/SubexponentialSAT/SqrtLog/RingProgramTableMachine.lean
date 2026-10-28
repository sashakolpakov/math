import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableBridge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 8 42

def state (regs : Fin 8 → Bool) (s : Store) (table : List Bool) : Data :=
  ⟨regs, fun i => if h : i.val < 27 then tapes s ⟨i.val, h⟩
    else if i.val = 27 then table else []⟩

def prepPorts : Fin 27 → Fin 42 := Fin.castAdd 15
def layoutPorts : Fin 18 → Fin 42 :=
  ![25, 22, 12, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
def layoutRegisters : Fin 2 → Fin 8 := ![1, 3]

theorem prepPorts_injective : Function.Injective prepPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 42 => x.val) h)
theorem layoutPorts_injective : Function.Injective layoutPorts := by decide
theorem layoutRegisters_injective : Function.Injective layoutRegisters := by decide

def combineRegs (regs : Fin 8 → Bool) (localRegs : Fin 2 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 1 (localRegs 0)) 3 (localRegs 1)

@[simp] theorem combineRegs_self (regs : Fin 8 → Bool) :
    combineRegs regs ![regs 1, regs 3] = regs := by simp [combineRegs]

theorem embed_prep (regs oldRegs : Fin 8 → Bool) (s old : Store) (table : List Bool) :
    embedState id prepPorts (state oldRegs old table) (RingProgramTable.state regs s) =
      state regs s table := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id prepPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; simp [state, prepPorts]
  · intro i hi
    have hg : ¬i.val < 27 := by
      intro h
      exact hi ⟨⟨i.val,h⟩, Fin.ext rfl⟩
    simp [state, hg]

theorem embed_layout (regs : Fin 8 → Bool) (lr : Fin 2 → Bool)
    (s : Store) (old table : List Bool) :
    embedState layoutRegisters layoutPorts (state regs s old)
      (RingTableLayout.state lr {(RingTableLayout.initial s.powers s.degree s.width) with out := table}) =
      state (combineRegs regs lr) s table := by
  apply embedState_eq_of_ports _ _ _ _ _ layoutRegisters_injective layoutPorts_injective
  · intro i; fin_cases i <;> simp [state, combineRegs, RingTableLayout.state, layoutRegisters]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0,h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1,h.symm⟩
    simp [state, combineRegs, h1, h3]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hn : i.val ≠ 27 := by
      intro h
      exact hi ⟨3, Fin.ext h.symm⟩
    simp [state, hn]

abbrev prep : Cmd 8 42 := .call (ProgramLinking.liftProgram RingProgramTable.program id prepPorts)
abbrev layout : Cmd 8 42 := .call (ProgramLinking.liftProgram RingTableLayout.program layoutRegisters layoutPorts)
abbrev command : Cmd 8 42 := .seq prep layout

theorem layout_eval {B d : ℕ} (P : ℕ → Fin d → Word B)
    (s : Store) (regs : Fin 8 → Bool)
    (hp : s.powers = (RingTableLayout.powerRecords P (2*d-1)).flatten)
    (hd : s.degree.length = d) (hw : s.width.length = B) :
    ∃ n ≤ RingTableLayout.budget d B+1, ∃ rf, Eval layout n
      (state regs s [])
      (state rf s (RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k))) := by
  obtain ⟨lr,n,hn,ht⟩ := RingTableLayout.power_table_program_run P s.degree s.width ![regs 1,regs 3] hd hw
  rw [← hp] at ht
  have he := eval_call_lifted RingTableLayout.program layoutRegisters layoutPorts
    (state regs s []) layoutRegisters_injective layoutPorts_injective ht
  have hi : embedState layoutRegisters layoutPorts (state regs s [])
      (RingTableLayout.state ![regs 1,regs 3]
        (RingTableLayout.initial s.powers s.degree s.width)) = state regs s [] := by
    simpa only [combineRegs_self] using embed_layout regs ![regs 1,regs 3] s [] []
  rw [hi] at he
  refine ⟨n,hn,combineRegs regs lr,?_⟩
  have hout := embed_layout regs lr s []
    (RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k))
  rw [hout] at he
  simpa only [layout] using he

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t)
    (ho : SubexponentialSAT.BinaryArithmetic.toNat cache.one.val < p^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ preparationBudget (baseWidth p t) d + RingTableLayout.budget d (baseWidth p t)+2,
      ∃ rf, Eval command n
      (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
      (state rf (ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
        c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne)
        (RingTriple.tableEncoding (RingProgram.structureTableRun
          (RingProgram.scalarProgram p t M cache) c.get).1)) := by
  obtain ⟨ri,ni,hni,ht⟩ := RingProgramTable.program_run p t M hd c cache.one cache.zero cache.minusOne s regs hmod hw hdegree
  let final := ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
    c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne
  have he := eval_call_lifted RingProgramTable.program id prepPorts
    (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
    Function.injective_id prepPorts_injective ht
  have he' : Eval prep ni (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
      (state ri final []) := by
    simpa only [prep, embed_prep, final] using he
  let P := fun j => (iterData p t M cache.zero cache.minusOne c j (initialData d cache.one cache.zero)).coefficients.get
  obtain ⟨nl,hnl,rf,hl⟩ := layout_eval P final ri
    (allPowerBits_eq_powerRecords p t M hd c cache.one cache.zero cache.minusOne) hdegree hw
  rw [nativeTable_eq_callback p t M cache hd c hz ho] at hl
  exact ⟨ni+nl, by omega, rf, he'.seq hl⟩

def program := compiled command 27 0

theorem nativeBudget_polynomial (B d : ℕ) :
    preparationBudget B d + RingTableLayout.budget d B + 3 ≤
      52000*(d+1)^5*(B+1)^2 := by
  have hp := preparationBudget_polynomial B d
  have hl := RingTableLayout.budget_polynomial d B
  have hd : (d+1)^2 ≤ (d+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hb : B+1 ≤ (B+1)^2 := by nlinarith
  have hbig : 1 ≤ (d+1)^5*(B+1)^2 := Nat.succ_le_of_lt (by positivity)
  have hpp : 50000*(d+1)^2*(B+1)^2 ≤ 50000*(d+1)^5*(B+1)^2 := by gcongr
  have hlp : 1000*(d+1)^5*(B+1) ≤ 1000*(d+1)^5*(B+1)^2 := by gcongr
  nlinarith


theorem program_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t)
    (ho : SubexponentialSAT.BinaryArithmetic.toNat cache.one.val < p^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn program
      (preparationBudget (baseWidth p t) d + RingTableLayout.budget d (baseWidth p t)+3)
      ((state regs (initialStore s c cache.one cache.zero cache.minusOne) []).withPC (some program.entry))
      ((state rf (ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
        c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne)
        (RingTriple.tableEncoding (RingProgram.structureTableRun
          (RingProgram.scalarProgram p t M cache) c.get).1)).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval p t M cache hd c hz ho s regs hmod hw hdegree
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 27 0⟩

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

end OAI.Algorithms
