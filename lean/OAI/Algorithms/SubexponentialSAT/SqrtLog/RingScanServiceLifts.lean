import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def serviceExpandPorts : Fin 16 → Fin 32 :=
  ![8, 9, 20, 21, 23, 24, 25, 26, 27, 11, 28, 29, 30, 12, 13, 14]
def serviceCountPorts : Fin 4 → Fin 32 := ![11, 15, 16, 19]
def serviceContractPorts : Fin 20 → Fin 32 := Fin.castAdd 12

theorem serviceExpandPorts_injective : Function.Injective serviceExpandPorts := by decide
theorem serviceCountPorts_injective : Function.Injective serviceCountPorts := by decide
theorem serviceContractPorts_injective : Function.Injective serviceContractPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

abbrev serviceExpand : Cmd 8 32 := .call
  (ProgramLinking.liftProgram RingTriple.program loadRegisters serviceExpandPorts)
abbrev serviceCount : Cmd 8 32 := .call
  (ProgramLinking.liftProgram countSquareProgram loadRegisters serviceCountPorts)
abbrev serviceContract : Cmd 8 32 := .call
  (ProgramLinking.liftProgram contractVectorProgram id serviceContractPorts)

private theorem embed_expand_service (regs : Fin 8 → Bool) (r : Fin 2 → Bool)
    (s : ServiceStore) (table stream : List Bool) :
    embedState loadRegisters serviceExpandPorts (serviceWorkState regs s)
      (RingTriple.state r {(RingTriple.layout s.x s.y s.degree s.width) with table := table, xs := stream}) =
    serviceWorkState (Function.update (Function.update regs 1 (r 0)) 3 (r 1))
      {s with tableWork := table, stream := stream, reverseStream := []} := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective serviceExpandPorts_injective
  · intro i; fin_cases i <;> simp [loadRegisters, RingTriple.state, serviceWorkState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [serviceWorkState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h20 : i ≠ 20 := fun h => hi ⟨2, h.symm⟩
    have h21 : i ≠ 21 := fun h => hi ⟨3, h.symm⟩
    have h23 : i ≠ 23 := fun h => hi ⟨4, h.symm⟩
    simp [serviceWorkState, serviceTapes, h20, h21, h23]

private theorem embed_count_service (regs : Fin 8 → Bool) (r : Fin 2 → Bool)
    (s : ServiceStore) (inner : List Bool) :
    embedState loadRegisters serviceCountPorts (serviceWorkState regs s)
      (countState r s.degree [] inner) =
    serviceWorkState (Function.update (Function.update regs 1 (r 0)) 3 (r 1))
      {s with outer := [], inner := inner} := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective serviceCountPorts_injective
  · intro i; fin_cases i <;> simp [loadRegisters, serviceWorkState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [serviceWorkState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h15 : i ≠ 15 := fun h => hi ⟨1, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨2, h.symm⟩
    simp [serviceWorkState, serviceTapes, h15, h16]

private theorem embed_contract_service (oldRegs regs : Fin 8 → Bool)
    (s : ServiceStore) (result stream outer inner : List Bool) :
    embedState id serviceContractPorts (serviceWorkState oldRegs s)
      (contractState regs s.modulus result stream [] s.width outer inner s.zero []) =
    serviceWorkState regs {s with result := result, x := [], y := stream, degree := [], outer := outer, inner := inner} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id serviceContractPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨15, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨16, h.symm⟩
    simp [serviceWorkState, serviceTapes, h0, h8, h9, h11, h15, h16]

theorem serviceExpand_eval {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (regs : Fin 8 → Bool)
    (modulus result degree width zero inner outer : List Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ n ≤ RingTriple.expandBudget B d + 1, ∃ rf,
      Eval serviceExpand n
        (serviceWorkState regs ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
          degree, width, zero, RingTriple.tableEncoding table, outer, inner,
          RingTriple.tableEncoding table, [], []⟩)
        (serviceWorkState rf ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
          degree, width, zero, RingTriple.tableEncoding table, outer, inner,
          [], [], blockBits (multiplicationBlocks table x y)⟩) := by
  obtain ⟨rf, n, hn, ht⟩ := RingTriple.expansion_native table x y degree width ![regs 1, regs 3] hd hw
  let s : ServiceStore := ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
    degree, width, zero, RingTriple.tableEncoding table, outer, inner,
    RingTriple.tableEncoding table, [], []⟩
  let a := RingTriple.state (![regs 1, regs 3] : Fin 2 → Bool)
    {(RingTriple.layout s.x s.y s.degree s.width) with table := s.tableWork, xs := []}
  let b := RingTriple.state rf
    {(RingTriple.layout s.x s.y s.degree s.width) with table := [], xs := blockBits (multiplicationBlocks table x y)}
  have he := eval_call_lifted RingTriple.program loadRegisters serviceExpandPorts
    (serviceWorkState regs s) loadRegisters_injective serviceExpandPorts_injective
    (a := a) (b := b) ht
  dsimp only [a, b] at he
  rw [embed_expand_service, embed_expand_service] at he
  refine ⟨n, hn, Function.update (Function.update regs 1 (rf 0)) 3 (rf 1), ?_⟩
  simpa only [s, Matrix.cons_val_zero, Matrix.cons_val_one, Function.update_eq_self] using he

theorem serviceCount_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    ∃ rf, Eval serviceCount (7*s.degree.length^2+14*s.degree.length+8)
      (serviceWorkState regs {s with outer := [], inner := []})
      (serviceWorkState rf {s with outer := [], inner := repeatCount s.degree s.degree.length}) := by
  obtain ⟨rf, ht⟩ := countSquareProgram_trace ![regs 1, regs 3] s.degree
  have he := eval_call_lifted countSquareProgram loadRegisters serviceCountPorts
    (serviceWorkState regs {s with outer := [], inner := []})
    loadRegisters_injective serviceCountPorts_injective ht
  refine ⟨Function.update (Function.update regs 1 (rf 0)) 3 (rf 1), ?_⟩
  have hs : Function.update (Function.update regs 1 (regs 1)) 3 (regs 3) = regs := by simp
  simpa only [embed_count_service, Matrix.cons_val_zero, Matrix.cons_val_one, hs] using he

theorem serviceContract_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (width outer inner : List Bool)
    (ho : outer.length = d) (hi : inner.length = d*d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ d*(d*d*(18000*(baseWidth p t+1)^2+48*baseWidth p t+51)+13*baseWidth p t+18)+6,
      ∃ rf, Eval serviceContract n
      (serviceWorkState regs ⟨M.bits, [], [], blockBits (multiplicationBlocks table x y),
        [], width, cache.zero.val, RingTriple.tableEncoding table, outer, inner, [], [], []⟩)
      (serviceWorkState rf ⟨M.bits,
        RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1,
        [], [], [], width, cache.zero.val, RingTriple.tableEncoding table, [], inner, [], [], []⟩) := by
  obtain ⟨rf, n, hn, ht⟩ := mulRun_contract_native p t M cache hz table x y regs width [] outer inner ho hi hw
  simp only [List.append_nil] at ht
  let s : ServiceStore := ⟨M.bits, [], [], blockBits (multiplicationBlocks table x y),
        [], width, cache.zero.val, RingTriple.tableEncoding table, outer, inner, [], [], []⟩
  let a := contractState regs s.modulus [] s.y [] s.width s.outer s.inner s.zero []
  let b := contractState rf s.modulus
    (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
    [] [] s.width [] s.inner s.zero []
  have he := eval_call_lifted contractVectorProgram id serviceContractPorts (serviceWorkState regs s)
    Function.injective_id serviceContractPorts_injective (a := a) (b := b) ht
  dsimp only [a, b] at he
  rw [embed_contract_service, embed_contract_service] at he
  exact ⟨n, hn, rf, by simpa only [s] using he⟩


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
