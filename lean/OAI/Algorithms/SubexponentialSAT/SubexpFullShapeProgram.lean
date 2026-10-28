import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.ChunkPartition

namespace OAI.Algorithms

/-!
# The physical shape for the uniform padded chunk array

The existing fixed block-copy program is used with a chunk-width word as its
table and an actual unary chunk count as its loop counter. It produces a word
of length `D * ell`, preserves the width word, and consumes the count. Caller
data such as the declared-variable shape are preserved through fixed port maps.
-/

namespace SubexponentialSAT.SubexpFullShapeProgram

open BitProgram StructuredCalls

abbrev program : Program 3 4 12 := Subexp.BlockCopyProgram.program

def fullShape (D : ℕ) (ell : List Bool) : List Bool :=
  Subexp.BlockCopyProgram.copies D ell

/-- Width on 0, empty output 1 and scratch 2, actual unary count on 3. -/
def inputState (D : ℕ) (ell : List Bool) : StructuredProgram.State 3 4 :=
  Subexp.BlockCopyProgram.initialState D ell []

/-- Width is preserved, the completed shape occupies 1, and work is empty. -/
def outputState (D : ℕ) (ell : List Bool) : StructuredProgram.State 3 4 :=
  Subexp.BlockCopyProgram.data false false ell (fullShape D ell) []

@[simp] theorem fullShape_length (D : ℕ) (ell : List Bool) :
    (fullShape D ell).length = D * ell.length :=
  Subexp.BlockCopyProgram.copies_length D ell

theorem fullShape_unary (D ell : ℕ) :
    fullShape D (List.replicate ell true) = List.replicate (D * ell) true := by
  induction D with
  | zero => simp [fullShape]
  | succ D ih =>
      change Subexp.BlockCopyProgram.copies (D + 1) (List.replicate ell true) = _
      rw [Subexp.BlockCopyProgram.copies_succ]
      change fullShape D (List.replicate ell true) ++ List.replicate ell true = _
      rw [ih, Nat.add_mul, Nat.one_mul, List.replicate_add]

@[simp] theorem output_width (D : ℕ) (ell : List Bool) :
    (outputState D ell).stacks 0 = ell := rfl

@[simp] theorem output_shape (D : ℕ) (ell : List Bool) :
    (outputState D ell).stacks 1 = fullShape D ell := rfl

@[simp] theorem output_scratch (D : ℕ) (ell : List Bool) :
    (outputState D ell).stacks 2 = [] := rfl

@[simp] theorem output_counter (D : ℕ) (ell : List Bool) :
    (outputState D ell).stacks 3 = [] := rfl

theorem trace (D : ℕ) (ell : List Bool) :
    @Trace 3 4 (size Subexp.BlockCopyProgram.command + 1)
      program (D * (7 * ell.length + 7) + 3)
      ((inputState D ell).withPC (some program.entry))
      ((outputState D ell).withPC none) := by
  simpa only [program, inputState, outputState, fullShape, List.append_nil] using
    Subexp.BlockCopyProgram.program_trace D ell []

/-- The same physical program can be placed in any fixed caller frame. -/
theorem lifted_eval {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 4 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (D : ℕ) (ell : List Bool) :
    Eval (.call (ProgramLinking.liftProgram program register stack))
      (D * (7 * ell.length + 7) + 3)
      (embedState register stack frame (inputState D ell))
      (embedState register stack frame (outputState D ell)) :=
  eval_call_lifted program register stack frame hregister hstack (trace D ell)

/-- In particular, a caller's `nShape` master stays unchanged when its port
is outside the four working ports. -/
theorem caller_stack_preserved {R S : ℕ} (register : Fin 3 → Fin R)
    (stack : Fin 4 → Fin S) (frame : StructuredProgram.State R S)
    (D : ℕ) (ell : List Bool) (nPort : Fin S)
    (hport : ¬ ∃ j, stack j = nPort) :
    (embedState register stack frame (outputState D ell)).stacks nPort =
      (embedState register stack frame (inputState D ell)).stacks nPort := by
  rw [embedState_stack_frame register stack frame (outputState D ell) nPort hport,
    embedState_stack_frame register stack frame (inputState D ell) nPort hport]

theorem primitive_execution (D : ℕ) (ell : List Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (D * (7 * ell.length + 7) + 3))
      (primitiveCfg program ((inputState D ell).withPC (some program.entry)))
      (primitiveCfg program ((outputState D ell).withPC none)) :=
  primitive_trace program (trace D ell)

/-- Ceiling-sized allocation contains every input bit and fewer than one
extra chunk of padding, including when the input has no variables. -/
theorem canonical_length_bounds (n : ℕ) (ell : List Bool) (hell : 0 < ell.length) :
    n ≤ (fullShape (ChunkPartition.count n ell.length) ell).length ∧
      (fullShape (ChunkPartition.count n ell.length) ell).length < n + ell.length := by
  simp only [fullShape_length]
  refine ⟨ChunkPartition.le_count_mul hell, ?_⟩
  have h := Nat.div_mul_le_self (n + ell.length - 1) ell.length
  change ChunkPartition.count n ell.length * ell.length < n + ell.length
  unfold ChunkPartition.count
  omega

end SubexponentialSAT.SubexpFullShapeProgram

end OAI.Algorithms
