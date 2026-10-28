import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def registers (n : ℕ) (hn : n ≤ 40) (i : Fin n) : Fin 40 := ⟨i.val,by omega⟩
def block (base n : ℕ) (hn : base+n ≤ 768) (i : Fin n) : Fin 768 :=
  ⟨base+i.val,by omega⟩
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

def bank := block 340 77 (by decide)
def early := block 417 77 (by decide)
def scopes := block 500 80 (by decide)
def high := block 580 32 (by decide)
def stats := block 612 21 (by decide)
def arity := block 633 12 (by decide)
def mask : Fin 4 → Fin 768 := ![338,645,719,646]
def finish : Fin 3 → Fin 768 := ![613,629,642]

def inputPorts : List (Fin 768) := [700,701,705,706,707,708,709]
def persistentOutputs : List (Fin 768) := [338,719,704,718]
def privatePorts : List (Fin 768) := (List.finRange 263).map (block 417 263 (by decide))
def bankPorts : List (Fin 768) := (List.finRange 77).map bank

theorem mask_injective : Function.Injective mask := by decide
theorem finish_injective : Function.Injective finish := by decide

theorem private_bounds (i : Fin 768) : i ∈ privatePorts ↔ 417 ≤ i.val ∧ i.val < 680 := by
  simp only [privatePorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; dsimp [block]; omega
  · intro h; exact ⟨⟨i.val-417,by omega⟩,Fin.ext (by dsimp [block]; omega)⟩

theorem private_disjoint_inputs : List.Disjoint privatePorts inputPorts := by
  apply List.disjoint_left.mpr
  intro i hi hj
  have h := (private_bounds i).mp hi
  simp only [inputPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
