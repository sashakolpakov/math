import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] query count compare
  SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

/-- Reverse order is the physical stack order; reversing gives coordinates
`0, ..., n-1`. Unused coordinates have degree zero and are retained in the mask. -/
def highPrefix (scopes : List (List ℕ)) (cut : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => decide (cut < degree scopes n) :: highPrefix scopes cut n

@[simp] theorem highPrefix_length (scopes : List (List ℕ)) (cut n : ℕ) :
    (highPrefix scopes cut n).length = n := by
  induction n <;> simp [highPrefix, *]

def scanPorts : UnaryForPrograms.Ports 10 16 where
  counter := 15
  bit := 0
  flag := 1

def scan : Code := UnaryForPrograms.forCmd scanPorts query

def scanInvariant (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool)
    (i : ℕ) (d : Data) : Prop :=
  ∃ regs fuel, d = state regs scopes i cut (highPrefix scopes cut i ++ mask) fuel

theorem state_fuel_other (regs regs' : Fin 10 → Bool) (scopes : List (List ℕ))
    (i cut : ℕ) (mask fuel fuel' : List Bool) (j : Fin 16) (hj : j ≠ 15) :
    (state regs scopes i cut mask fuel).stacks j =
      (state regs' scopes i cut mask fuel').stacks j := by
  fin_cases j <;> first | exact (hj rfl).elim |
    simp only [state, Matrix.cons_val_succ', Matrix.cons_val_zero']

theorem state_fuel (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (i cut : ℕ) (mask fuel : List Bool) :
    (state regs scopes i cut mask fuel).stacks 15 = fuel := by
  change (state regs scopes i cut mask fuel).stacks ⟨15, by decide⟩ = fuel
  simp only [state, Matrix.cons_val_succ', Matrix.cons_val_zero']

theorem scanInvariant_stable (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool) :
    UnaryForPrograms.FrameStable scanPorts (scanInvariant scopes cut mask) := by
  intro i a b heq hi
  obtain ⟨regs, fuel, ha⟩ := hi
  refine ⟨b.regs, b.stacks 15, ?_⟩
  apply CounterForPrograms.data_ext (a := b)
    (b := state b.regs scopes i cut (highPrefix scopes cut i ++ mask) (b.stacks 15)) rfl
  funext j
  by_cases hj : j = 15
  · subst j
    exact (state_fuel _ _ _ _ _ _).symm
  · have h := heq j hj
    rw [ha] at h
    exact h.symm.trans (state_fuel_other regs b.regs scopes i cut
      (highPrefix scopes cut i ++ mask) fuel (b.stacks 15) j hj)

theorem query_bodySpec (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool) :
    UnaryForPrograms.BodySpec scanPorts query (scanInvariant scopes cut mask)
      (fun i => queryBudget scopes i cut) := by
  intro i d hi
  obtain ⟨regs, fuel, hd⟩ := hi
  obtain ⟨n, rf, hn, he⟩ := query_eval regs scopes i cut
    (highPrefix scopes cut i ++ mask) fuel
  refine ⟨n, state rf scopes (i+1) cut
    (decide (cut < degree scopes i) :: (highPrefix scopes cut i ++ mask)) fuel,
    hn, ?_, ?_, rf, fuel, rfl⟩
  · rw [hd]
    exact he
  · rw [hd]
    change (state rf scopes (i+1) cut
      (decide (cut < degree scopes i) :: (highPrefix scopes cut i ++ mask)) fuel).stacks 15 =
      (state regs scopes i cut (highPrefix scopes cut i ++ mask) fuel).stacks 15
    rw [state_fuel, state_fuel]

def scanBudget (scopes : List (List ℕ)) (n cut : ℕ) : ℕ :=
  CounterForPrograms.budgetSum (fun i => queryBudget scopes i cut) 0 n + 2 * n + 2

theorem scan_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n cut : ℕ) (mask : List Bool) :
    ∃ time rf, time ≤ scanBudget scopes n cut ∧
      Eval scan time (state regs scopes 0 cut mask (unary n))
        (state rf scopes n cut (highPrefix scopes cut n ++ mask) []) := by
  let a := state regs scopes 0 cut mask (unary n)
  obtain ⟨time, b, he, hb, hf, ht⟩ := UnaryForPrograms.for_correct scanPorts query
    (scanInvariant scopes cut mask) (fun i => queryBudget scopes i cut)
    (scanInvariant_stable scopes cut mask) (query_bodySpec scopes cut mask) a
    ⟨regs, unary n, rfl⟩
  have hlen : (a.stacks scanPorts.counter).length = n := by simp [a, state, scanPorts]
  rw [hlen] at hb ht
  obtain ⟨rf, fuel, hbeq⟩ := hb
  have hfu : fuel = [] := by simpa [hbeq, state, scanPorts] using hf
  subst fuel
  exact ⟨time, rf, ht, by simpa only [scan, hbeq] using he⟩


def scanProgram := compiled scan 0 14

theorem scanProgram_runsIn (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n cut : ℕ) (mask : List Bool) :
    ∃ rf, RunsIn scanProgram (scanBudget scopes n cut + 1)
      ((state regs scopes 0 cut mask (unary n)).withPC (some scanProgram.entry))
      ((state rf scopes n cut (highPrefix scopes cut n ++ mask) []).withPC none) := by
  obtain ⟨time, rf, ht, he⟩ := scan_eval regs scopes n cut mask
  exact ⟨rf, time + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 14⟩


def uniformQueryBudget (scopes : List (List ℕ)) (n cut : ℕ) :=
  1000 * ((scopeBits scopes).length + scopes.length + n + 1)^2 +
    20 * (cut + scopes.length + 2) + 20

theorem queryBudget_le (scopes : List (List ℕ)) (n cut v : ℕ) (hv : v ≤ n) :
    queryBudget scopes v cut ≤ uniformQueryBudget scopes n cut := by
  have hb := SubexpIncidenceSlotProgram.budget_le scopes scopes.length v
    ((scopeBits scopes).length + scopes.length + n)
    (by change (scopeBits scopes).length ≤ _; omega) (by omega) (by omega)
  have hd : degree scopes v ≤ scopes.length := by
    simpa only [degree, Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices] using
      SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
  dsimp [queryBudget, uniformQueryBudget]
  omega


theorem scanBudget_le (scopes : List (List ℕ)) (n cut : ℕ) :
    scanBudget scopes n cut + 1 ≤ n * (uniformQueryBudget scopes n cut + 2) + 3 := by
  have h := CounterForPrograms.budgetSum_le (fun i => queryBudget scopes i cut)
    0 n (uniformQueryBudget scopes n cut) (by
      intro i hi hlt
      exact queryBudget_le scopes n cut i (by omega))
  dsimp [scanBudget]
  nlinarith

/-- One fixed primitive bit machine, polynomial in actual encoded scopes,
original ambient dimension, and the supplied integer cutoff. -/
theorem scanProgram_primitive (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n cut : ℕ) (mask : List Bool) :
    ∃ rf, Computation.RunsIn (primitive scanProgram).step
      (primitiveOverhead scanProgram * (n * (uniformQueryBudget scopes n cut + 2) + 3))
      (primitiveCfg scanProgram
        ((state regs scopes 0 cut mask (unary n)).withPC (some scanProgram.entry)))
      (primitiveCfg scanProgram
        ((state rf scopes n cut (highPrefix scopes cut n ++ mask) []).withPC none)) := by
  obtain ⟨rf, hr⟩ := scanProgram_runsIn regs scopes n cut mask
  exact ⟨rf, BitProgram.primitive_execution scanProgram (hr.mono (scanBudget_le scopes n cut))⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
