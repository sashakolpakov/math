import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepareOps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramScan

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def initial (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) : Data :=
  ⟨regs, fun i => if i = 0 then scopeBits scopes else
    if i = 16 then n else if i = 17 then t else []⟩

def records (scopes : List (List ℕ)) := (Mass.scopeRecords scopes).map Mass.encode
def mass (scopes : List (List ℕ)) := (scopes.map List.length).sum
def cut (scopes : List (List ℕ)) (n t : List Bool) :=
  (mass scopes * BinaryArithmetic.toNat t) ⌈/⌉ BinaryArithmetic.toNat n
def scanPorts : Fin 16 → Fin 32 := Fin.castAdd 16
theorem scanPorts_inj : Function.Injective scanPorts := Fin.castAdd_injective _ _
def scanCall : Code := liftCommand scan 0 14 id scanPorts

def command : Code := .seq countCall (.seq massCall (.seq binaryCall
  (.seq cutoffCall (.seq unaryCall (.seq bump (.seq fuelCall scanCall))))))
def program := compiled command 0 14

def unarySized (value size : ℕ) := 7 * size + 5 + 32 * (value + 1) * (size + 1) + 1
theorem unaryBound_le (bits : List Bool) (value size : ℕ)
    (hv : BinaryArithmetic.toNat bits = value) (hl : bits.length ≤ size) :
    SubexpClauseMastersProgram.unaryCopyBound bits + 1 ≤ unarySized value size := by
  simp only [SubexpClauseMastersProgram.unaryCopyBound, CounterConversions.runtimeBound,
    CounterPrograms.value_eq_toNat, hv, unarySized]
  gcongr

def budget (scopes : List (List ℕ)) (n t : List Bool) :=
  (SubexpScopeCountSetup.countBudget (records scopes) + 1) +
  MassPreserve.bound (scopeBits scopes) + (SubexpFactorCountSetup.countBudget (mass scopes) + 1) +
  Cutoff.bound (List.replicate (mass scopes) false) t n +
  unarySized (cut scopes n t) (mass scopes + t.length + 2) + 2 +
  unarySized (BinaryArithmetic.toNat n) n.length + scanBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 1

theorem records_bits (scopes : List (List ℕ)) :
    Encoding.encodeList id (records scopes) = scopeBits scopes :=
  Mass.encoded_scopeRecords scopes
theorem records_length (scopes : List (List ℕ)) : (records scopes).length = scopes.length := by
  simp [records, Mass.scopeRecords]

/-- Full prefix trace. Persistent input words and source scopes are retained;
output14 is the mask, output2 is unary n, and output13 is unary(cut+1).
Computed E1, unary S18, binary S19 and cutoff20 remain in their work ports.
Arithmetic work24--31 may contain leftovers and is outside the scan frame. -/
theorem command_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    ∃ time b, Eval command time (initial regs scopes n t) b ∧
      time ≤ budget scopes n t ∧
      b.stacks 0 = scopeBits scopes ∧ b.stacks 16 = n ∧ b.stacks 17 = t ∧
      b.stacks 14 = highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ∧
      b.stacks 2 = unary (BinaryArithmetic.toNat n) ∧ b.stacks 13 = unary (cut scopes n t + 1) ∧
      b.stacks 15 = [] := by
  let a := initial regs scopes n t
  obtain ⟨re, he⟩ := count_eval a (records scopes)
    (by simpa [a, initial] using (records_bits scopes).symm) (by simp [a, initial])
    (by simp [a, initial]) (by simp [a, initial])
  let e : Data := ⟨re, Function.update a.stacks 1 (unary scopes.length)⟩
  rw [records_length] at he
  obtain ⟨tm, rm, hm, htm⟩ := mass_eval e scopes
    (by simp [e, a, initial]) (by simp [e, a, initial]) (by simp [e, a, initial])
    (by simp [e, a, initial]) (by simp [e, a, initial])
  let m : Data := ⟨rm, Function.update e.stacks 18 (unary (mass scopes))⟩
  obtain ⟨tb, rb, bits, hb, htb, hvb, hlb⟩ := binary_eval m
    (by simp [m, e, a, initial]) (by simp [m, e, a, initial]) (by simp [m, e, a, initial])
  have hvb' : BinaryArithmetic.toNat bits = mass scopes := by simpa [m] using hvb
  have hlb' : bits.length ≤ mass scopes := by simpa [m] using hlb
  let v : Data := ⟨rb, Function.update m.stacks 19 bits⟩
  have hv16 : v.stacks 16 = n := by simp [v, m, e, a, initial]
  have hv17 : v.stacks 17 = t := by simp [v, m, e, a, initial]
  have hv19 : v.stacks 19 = bits := by simp [v]
  obtain ⟨tc, c, hc, htc, hvc, hlc, hframe⟩ := cutoff_eval v (by simpa [hv16] using hn) (by
    intro i hi0 hi1 hi2
    fin_cases i <;> first | exact (hi0 rfl).elim | exact (hi1 rfl).elim |
      exact (hi2 rfl).elim | simp [cutoffPorts, v, m, e, a, initial])
  have hvc' : BinaryArithmetic.toNat (c.stacks 20) = cut scopes n t := by
    simpa only [hv16, hv17, hv19, hvb', cut] using hvc
  have hlc' : (c.stacks 20).length ≤ mass scopes + t.length + 2 := by
    rw [hv19, hv17] at hlc
    omega
  have hcsmall (i : Fin 32) (hi : i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
      i = 21 ∨ i = 22 ∨ i = 23) : c.stacks i = v.stacks i := hframe i hi
  obtain ⟨tu, ru, hu, htu⟩ := unary_eval unaryPorts unaryPorts_inj c
    (by change c.stacks 13 = []; rw [hcsmall 13 (Or.inl (by decide))]; simp [v, m, e, a, initial])
    (by change c.stacks 21 = []; rw [hcsmall 21 (by simp)]; simp [v, m, e, a, initial])
    (by change c.stacks 22 = []; rw [hcsmall 22 (by simp)]; simp [v, m, e, a, initial])
    (by change c.stacks 23 = []; rw [hcsmall 23 (by simp)]; simp [v, m, e, a, initial])
  change Eval unaryCall tu c ⟨ru, Function.update c.stacks 13 (unary (BinaryArithmetic.toNat (c.stacks 20)))⟩ at hu
  rw [hvc'] at hu
  let u : Data := ⟨ru, Function.update c.stacks 13 (unary (cut scopes n t))⟩
  let p : Data := ⟨Function.update u.regs 0 true,
    Function.update u.stacks 13 (unary (cut scopes n t + 1))⟩
  have hp : Eval bump 2 u p := by
    simpa [p, u, unary, List.replicate_succ] using bump_eval u
  obtain ⟨tf, rf, hf, htf⟩ := unary_eval fuelPorts fuelPorts_inj p
    (by change p.stacks 15 = []; simp only [p, u, Function.update_of_ne (by decide : (15 : Fin 32) ≠ 13)];
        rw [hcsmall 15 (Or.inl (by decide))]; simp [v, m, e, a, initial])
    (by change p.stacks 21 = []; simp only [p, u, Function.update_of_ne (by decide : (21 : Fin 32) ≠ 13)];
        rw [hcsmall 21 (by simp)]; simp [v, m, e, a, initial])
    (by change p.stacks 22 = []; simp only [p, u, Function.update_of_ne (by decide : (22 : Fin 32) ≠ 13)];
        rw [hcsmall 22 (by simp)]; simp [v, m, e, a, initial])
    (by change p.stacks 23 = []; simp only [p, u, Function.update_of_ne (by decide : (23 : Fin 32) ≠ 13)];
        rw [hcsmall 23 (by simp)]; simp [v, m, e, a, initial])
  have hp16 : p.stacks 16 = n := by simp [p, u, hcsmall 16 (by simp), hv16]
  change Eval fuelCall tf p ⟨rf, Function.update p.stacks 15 (unary (BinaryArithmetic.toNat (p.stacks 16)))⟩ at hf
  rw [hp16] at hf
  let f : Data := ⟨rf, Function.update p.stacks 15 (unary (BinaryArithmetic.toNat n))⟩
  have hproject : projectState id scanPorts f =
      state f.regs scopes 0 (cut scopes n t) [] (unary (BinaryArithmetic.toNat n)) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i
    have hi : (scanPorts i).val < 16 := i.isLt
    have hci := hcsmall (scanPorts i) (Or.inl hi)
    fin_cases i <;> simp [ scanPorts, f, p, u] <;>
      simpa [scanPorts, v, m, e, a, initial] using hci
  obtain ⟨ts, rs, hts, hs⟩ := scan_eval f.regs scopes (BinaryArithmetic.toNat n) (cut scopes n t) []
  rw [← hproject] at hs
  let final := embedState id scanPorts f
    (state rs scopes (BinaryArithmetic.toNat n) (cut scopes n t) (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ++ []) [])
  have hs' := eval_liftCommand_from_state scan 0 14 id scanPorts f
    Function.injective_id scanPorts_inj hs
  have hfinal (i : Fin 16) : final.stacks (scanPorts i) =
      (state rs scopes (BinaryArithmetic.toNat n) (cut scopes n t) (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ++ []) []).stacks i :=
    embedState_stack _ _ _ _ scanPorts_inj i
  refine ⟨(SubexpScopeCountSetup.countBudget (records scopes) + 1) +
      (tm + (tb + (tc + (tu + (2 + (tf + (ts + 1))))))), final,
    he.seq (hm.seq (hb.seq (hc.seq (hu.seq (hp.seq (hf.seq hs')))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htm' : tm ≤ MassPreserve.bound (scopeBits scopes) := by simpa [scopeBits] using htm
    have htb' : tb ≤ SubexpFactorCountSetup.countBudget (mass scopes) + 1 := by simpa [m] using htb
    have htc' : tc ≤ Cutoff.bound (List.replicate (mass scopes) false) t n := by
      rw [hv19, hv17, hv16] at htc
      apply htc.trans
      unfold Cutoff.bound
      simp only [List.length_replicate]
      gcongr
    have htu' : tu ≤ unarySized (cut scopes n t) (mass scopes + t.length + 2) :=
      htu.trans (unaryBound_le _ _ _ hvc' hlc')
    have htf' : tf ≤ unarySized (BinaryArithmetic.toNat n) n.length := by
      change tf ≤ SubexpClauseMastersProgram.unaryCopyBound (p.stacks 16) + 1 at htf
      rw [hp16] at htf
      exact htf.trans (unaryBound_le n _ _ rfl le_rfl)
    unfold budget
    omega
  · exact hfinal 0
  · rw [embedState_stack_frame id scanPorts f _ 16 (by
        rintro ⟨i, hi⟩; have := congrArg Fin.val hi; dsimp [scanPorts] at this; omega)]
    simp [f, hp16]
  · rw [embedState_stack_frame id scanPorts f _ 17 (by
        rintro ⟨i, hi⟩; have := congrArg Fin.val hi; dsimp [scanPorts] at this; omega)]
    simp [f, p, u, hcsmall 17 (by simp), hv17]
  · simpa [scanPorts, state] using hfinal (14 : Fin 16)
  · exact hfinal 2
  · exact hfinal 13
  · exact hfinal 15

theorem runsIn (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    ∃ b : Data, RunsIn program (budget scopes n t + 1)
      ((initial regs scopes n t).withPC (some program.entry)) (b.withPC none) ∧
      b.stacks 14 = highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) := by
  obtain ⟨time, b, he, ht, _, _, _, hm, _⟩ := command_eval regs scopes n t hn
  exact ⟨b, ⟨time + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 14⟩, hm⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
