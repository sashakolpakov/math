import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Physical per-node Taylor workspace preparation

All inputs are copied from live masters. In particular, 5 and 10 must already
hold the target modulus and target base-width shape after source-row setup.
Master 126 holds unary R+1, and 255 holds the complete dense-row table.
The fixed cleanup table runs after the node template has consumed the cache.
-/

namespace SubexponentialSAT.SubexpNodeCacheSetup

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 256
abbrev Store := Fin 256 → List Bool
abbrev Move := Fin 256 × Fin 256

def copies : List Move → Cmd 16 256
  | [] => .base .skip
  | (src, dst) :: rest => .seq (.call (StackRoutines.copyProgram src dst 0 0 1)) (copies rest)

def copied : List Move → Data → Data
  | [], d => d
  | (src, dst) :: rest, d => copied rest (afterCopy d src dst 0 1)

def copyCost : List Move → Data → ℕ
  | [], _ => 0
  | (src, dst) :: rest, d => 7 * (d.stacks src).length + 5 +
      copyCost rest (afterCopy d src dst 0 1)

theorem copies_eval (moves : List Move) (d : Data)
    (h0 : d.stacks 0 = [])
    (hd : ∀ m ∈ moves, m.1 ≠ m.2 ∧ m.1 ≠ 0 ∧ m.2 ≠ 0) :
    Eval (copies moves) (copyCost moves d) d (copied moves d) := by
  induction moves generalizing d with
  | nil => exact .base (.skip d)
  | cons m rest ih =>
    rcases m with ⟨src, dst⟩
    have hs := hd (src, dst) (by simp)
    have hc := copy_eval d src dst 0 0 1 hs.1 hs.2.1 hs.2.2.symm (by decide) h0
    have ht : (afterCopy d src dst 0 1).stacks 0 = [] := by
      simpa [afterCopy, StackRoutines.copyStacks, hs.2.2.symm] using h0
    have hr := ih (afterCopy d src dst 0 1) ht (by
      intro m hm
      exact hd m (by simp [hm]))
    exact hc.seq hr

/-- Four charged width copies produce a shape of length 4B; the shape bits
are only tested for presence, so their values need not be normalized. -/
def preparationMoves : List Move :=
  [(255, 100), (126, 101), (5, 66), (91, 73), (10, 74),
    (10, 81), (10, 81), (10, 81), (10, 81)]

abbrev prepare : Cmd 16 256 := copies preparationMoves

def width4 (bits : List Bool) : List Bool := bits ++ bits ++ bits ++ bits

theorem width4_length (bits : List Bool) : (width4 bits).length = 4 * bits.length := by
  simp [width4]
  omega

def preparedStacks (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update s 100 (s 255)) 101 (s 126))
      66 (s 5)) 73 (s 91)) 74 (s 10)) 81 (width4 (s 10))

def prepared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, preparedStacks d.stacks⟩

def prepareCost (d : Data) : ℕ :=
  7 * ((d.stacks 255).length + (d.stacks 126).length + (d.stacks 5).length +
    (d.stacks 91).length + 5 * (d.stacks 10).length) + 45

theorem copied_preparation (d : Data)
    (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = []) :
    copied preparationMoves d = prepared d := by
  apply state_ext
  · simp [copied, preparationMoves, afterCopy, prepared, StackRoutines.readRegs_reset]
  · simp [copied, preparationMoves, afterCopy, prepared, preparedStacks,
      StackRoutines.copyStacks, h100, h101, h66, h73, h74, h81, width4, List.append_assoc]

theorem copyCost_preparation (d : Data) : copyCost preparationMoves d = prepareCost d := by
  simp [copyCost, preparationMoves, afterCopy, StackRoutines.copyStacks, prepareCost]
  omega

theorem prepare_eval (d : Data) (h0 : d.stacks 0 = [])
    (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = []) :
    Eval prepare (prepareCost d) d (prepared d) := by
  have h := copies_eval preparationMoves d h0 (by
    intro m hm
    simp only [preparationMoves, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide)
  simpa only [prepare, copyCost_preparation,
    copied_preparation d h100 h101 h66 h73 h74 h81] using h

theorem prepared_stack (d : Data) (i : Fin 256)
    (h100 : i ≠ 100) (h101 : i ≠ 101) (h66 : i ≠ 66)
    (h73 : i ≠ 73) (h74 : i ≠ 74) (h81 : i ≠ 81) :
    (prepared d).stacks i = d.stacks i := by
  simp [prepared, preparedStacks, h100, h101, h66, h73, h74, h81]

abbrev clear (src : Fin 256) : Cmd 16 256 := .call (StackRoutines.clearProgram src 0 1)

def clearOut (d : Data) (src : Fin 256) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 256) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (clearOut d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clear, clearOut, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

def clears : List (Fin 256) → Cmd 16 256
  | [] => .base .skip
  | i :: rest => .seq (clear i) (clears rest)

def cleared : List (Fin 256) → Data → Data
  | [], d => d
  | i :: rest, d => cleared rest (clearOut d i)

def clearCost : List (Fin 256) → Data → ℕ
  | [], _ => 0
  | i :: rest, d => 2 * (d.stacks i).length + 3 + clearCost rest (clearOut d i)

theorem clears_eval (ports : List (Fin 256)) (d : Data) :
    Eval (clears ports) (clearCost ports d) d (cleared ports d) := by
  induction ports generalizing d with
  | nil => exact .base (.skip d)
  | cons i rest ih => exact (clear_eval d i).seq (ih (clearOut d i))

theorem cleared_stacks (ports : List (Fin 256)) (d : Data) (i : Fin 256) :
    (cleared ports d).stacks i = if i ∈ ports then [] else d.stacks i := by
  induction ports generalizing d with
  | nil => simp [cleared]
  | cons j rest ih =>
    simp only [cleared, ih, List.mem_cons]
    by_cases hr : i ∈ rest
    · simp [hr]
    · by_cases hj : i = j
      · subst j; simp [hr, clearOut]
      · simp [hr, hj, clearOut]

/-- The cache must have been consumed into the node template before cleanup.
The node word and cache payload are physically cleared along with the copies. -/
def cleanupPorts : List (Fin 256) := [100, 101, 66, 73, 74, 81, 78, 102]

abbrev cleanup : Cmd 16 256 := clears cleanupPorts

def cleanupCost (d : Data) : ℕ :=
  2 * ((d.stacks 100).length + (d.stacks 101).length + (d.stacks 66).length +
    (d.stacks 73).length + (d.stacks 74).length + (d.stacks 81).length +
    (d.stacks 78).length + (d.stacks 102).length) + 24

theorem clearCost_cleanup (d : Data) : clearCost cleanupPorts d = cleanupCost d := by
  simp [clearCost, cleanupPorts, clearOut, cleanupCost]
  omega

theorem cleanup_eval (d : Data) :
    Eval cleanup (cleanupCost d) d (cleared cleanupPorts d) := by
  simpa only [cleanup, clearCost_cleanup] using clears_eval cleanupPorts d

theorem cleanup_stack (d : Data) (i : Fin 256) (hi : i ∈ cleanupPorts) :
    (cleared cleanupPorts d).stacks i = [] := by
  simp only [cleared_stacks, ite_eq_left hi]

theorem cleanup_frame (d : Data) (i : Fin 256) (hi : i ∉ cleanupPorts) :
    (cleared cleanupPorts d).stacks i = d.stacks i := by
  simp only [cleared_stacks, ite_eq_right hi]

abbrev prepareProgram : Program 16 256 (size prepare + 1) := compiled prepare 255 100
abbrev cleanupProgram : Program 16 256 (size cleanup + 1) := compiled cleanup 102 102

theorem prepare_trace (d : Data) (h0 : d.stacks 0 = [])
    (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = []) :
    Trace prepareProgram (prepareCost d + 1)
      (d.withPC (some prepareProgram.entry)) ((prepared d).withPC none) :=
  compiled_halt_trace (prepare_eval d h0 h100 h101 h66 h73 h74 h81) 255 100

theorem cleanup_trace (d : Data) :
    Trace cleanupProgram (cleanupCost d + 1)
      (d.withPC (some cleanupProgram.entry)) ((cleared cleanupPorts d).withPC none) :=
  compiled_halt_trace (cleanup_eval d) 102 102

end SubexponentialSAT.SubexpNodeCacheSetup

end OAI.Algorithms
