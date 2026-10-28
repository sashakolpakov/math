import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed physical layout for native ring preparation.

The local setup has 32 registers and 640 stacks.  It can be lifted into the
40-register/768-stack leaf caller.  The collector's stacks 320--339 are never
used.  Arithmetic metadata is written directly to its native consumer port;
temporary search, scalar, table, and node data have disjoint workspaces.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 32 640

def registers (n : ℕ) (h : n ≤ 32) : Fin n → Fin 32 :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem registers_injective (n : ℕ) (h : n ≤ 32) :
    Function.Injective (registers n h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin 32 => x.val) hij

/-- The runtime numerical bank is kept until every unary serialization and
node-count copy has finished. -/
def parameters (i : Fin 77) : Fin 640 := ⟨340 + i.val, by omega⟩

theorem parameters_injective : Function.Injective parameters := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [parameters] at this
  omega

/-- Search depth is the final native ring dimension.  The encoded F3
coefficient list on 195 is temporary; padding consumes it. -/
def search : Fin 28 → Fin 640 := fun i =>
  if i = 13 then 195 else if i = 14 then 204 else ⟨420 + i.val, by omega⟩

/-- Boot, scalar-cache construction, and (when needed) Newton preparation
share this local workspace.  The binary-t input remains a private copy. -/
def scalar : Fin 41 → Fin 640 := fun i =>
  if i = 5 then 194 else if i = 12 then 202 else
  if i = 17 then 203 else if i = 29 then 212 else ⟨480 + i.val, by omega⟩

/-- Padded coefficients remain at search port21 =441.  Scalar one is copied
to the consumed seed538; its canonical master at498 is preserved. -/
def table : Fin 42 → Fin 640 := fun i =>
  if i = 0 then 538 else if i = 5 then 194 else if i = 12 then 202 else
  if i = 17 then 508 else if i = 21 then 441 else if i = 22 then 204 else
  if i = 24 then 203 else if i = 27 then 201 else ⟨540 + i.val, by omega⟩

/-- Dynamic-d constant vectors have separate scratch from table generation.
Only their output location varies among full one, minus one, and zero. -/
def constant (out : Fin 640) : Fin 27 → Fin 640 := fun i =>
  if i = 0 then 538 else if i = 15 then out else if i = 22 then 204 else
  if i = 24 then 203 else ⟨584 + i.val, by omega⟩

def nodes : Fin 15 → Fin 640 := fun i =>
  if i = 12 then 256 else if i = 14 then 204 else ⟨612 + i.val, by omega⟩

theorem search_injective : Function.Injective search := by decide
theorem scalar_injective : Function.Injective scalar := by decide
theorem table_injective : Function.Injective table := by decide
theorem constant_one_injective : Function.Injective (constant 207) := by decide
theorem constant_minusOne_injective : Function.Injective (constant 211) := by decide
theorem constant_zero_injective : Function.Injective (constant 280) := by decide
theorem nodes_injective : Function.Injective nodes := by decide

/-- These are preservation statements about physical ports, independent of
all runtime values and dimensions. -/
theorem search_avoids_collector (i : Fin 28) :
    (search i).val < 320 ∨ 340 ≤ (search i).val := by
  fin_cases i <;> decide

theorem scalar_avoids_collector (i : Fin 41) :
    (scalar i).val < 320 ∨ 340 ≤ (scalar i).val := by
  fin_cases i <;> decide

theorem table_avoids_collector (i : Fin 42) :
    (table i).val < 320 ∨ 340 ≤ (table i).val := by
  fin_cases i <;> decide

theorem nodes_avoids_collector (i : Fin 15) :
    (nodes i).val < 320 ∨ 340 ≤ (nodes i).val := by
  fin_cases i <;> decide

/-- The closed idempotent program is run in a private workspace after the
ordinary ring setup. Its local cleanup therefore cannot clear native t or
other metadata. Repeating its scalar preparation has polynomial cost. -/
def idempotent (i : Fin 41) : Fin 640 := ⟨480+i.val, by omega⟩

theorem idempotent_injective : Function.Injective idempotent := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (fun x : Fin 640 => x.val) hij
  simp only [idempotent] at h
  omega

/-- Leave the parser/branch registers16--23 untouched when this setup is
called inside the agreed 40-register leaf ambient. -/
def wideRegisters (i : Fin 32) : Fin 40 :=
  if h : i.val < 16 then ⟨i.val, by omega⟩ else ⟨i.val+8, by omega⟩

def wideStacks (i : Fin 640) : Fin 768 := i.castLE (by decide)

theorem wideRegisters_injective : Function.Injective wideRegisters := by decide

theorem wideStacks_injective : Function.Injective wideStacks := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin 768 => x.val) hij

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
