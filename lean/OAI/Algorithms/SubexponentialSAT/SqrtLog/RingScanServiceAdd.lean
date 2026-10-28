import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def serviceAddPorts : Fin 15 → Fin 32 := Fin.castAdd 17

theorem serviceAddPorts_injective : Function.Injective serviceAddPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

abbrev serviceAdd : Cmd 8 32 := .call (ProgramLinking.liftProgram addVectorProgram id serviceAddPorts)

private theorem embed_serviceAdd (regs oldRegs : Fin 8 → Bool)
    (modulus result x y degree width zero table oldResult oldX oldY oldDegree : List Bool) :
    embedState id serviceAddPorts (serviceState oldRegs modulus oldResult oldX oldY oldDegree width zero table)
      (addState regs modulus result [] x y [] degree width) =
    serviceState regs modulus result x y degree width zero table := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id serviceAddPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    simp [serviceState, serviceWorkState, serviceTapes, h0, h8, h9, h11]

def serviceAddBudget (B d : ℕ) : ℕ := d*(6000*(B+1)^2+34*B+29)+6

/-- Common service ABI for addition. Caller context is preserved by a fixed
program lift, and every coefficient operation is included in the bound. -/
theorem serviceAdd_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width table : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ serviceAddBudget (baseWidth p t) d, ∃ rf, Eval serviceAdd n
      (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table)
      (serviceState rf M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] width cache.zero.val table) := by
  obtain ⟨rf, n, hn, ht⟩ := addRun_native p t M cache x y regs degree width hd hw
  have he := eval_call_lifted addVectorProgram id serviceAddPorts
    (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table)
    Function.injective_id serviceAddPorts_injective ht
  exact ⟨n, hn, rf, by simpa only [embed_serviceAdd] using he⟩

abbrev serviceAddProgram : Program 8 32 (size serviceAdd+1) := compiled serviceAdd 8 0

theorem serviceAddProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width table : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn serviceAddProgram (serviceAddBudget (baseWidth p t) d + 1)
      ((serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val table).withPC
        (some serviceAddProgram.entry))
      ((serviceState rf M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] width cache.zero.val table).withPC none) := by
  obtain ⟨n, hn, rf, ht⟩ := serviceAdd_eval p t M cache x y regs degree width table hd hw
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 8 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
