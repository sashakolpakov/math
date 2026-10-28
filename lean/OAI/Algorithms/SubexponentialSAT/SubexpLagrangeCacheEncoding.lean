import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketCoordinates
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Physical framing of a Lagrange coefficient row

The input is a flat array of equal-width coefficient words. The fixed
program reads the runtime coefficient count, frames every coefficient in
increasing degree order, and prepends the resulting row to the cache.
-/

namespace SubexponentialSAT.SubexpLagrangeCacheEncoding

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.TupleProgram

abbrev Word := List Bool
abbrev Data := State 5 11
abbrev Code := Cmd 5 11

def tapes (input width todo row acc scratch : Word) : Fin 11 → Word :=
  ![input, width, [], todo, [], [], [], [], row, acc, scratch]

def state (regs : Fin 5 → Bool) (input width todo row acc scratch : Word) : Data :=
  ⟨regs, tapes input width todo row acc scratch⟩

private theorem tapes_eq (input width todo row acc scratch : Word) :
    tapes input width todo row acc scratch = fun i =>
      if i = 0 then input else if i = 1 then width else if i = 3 then todo
      else if i = 8 then row else if i = 9 then acc else if i = 10 then scratch else [] := by
  funext i
  fin_cases i <;> rfl

def framePorts : Fin 9 → Fin 11 := Fin.castAdd 2
theorem framePorts_injective : Function.Injective framePorts := Fin.castAdd_injective _ _

def frame : Code :=
  .call (ProgramLinking.liftProgram SubexpTaylorFrames.program id framePorts)

private theorem embed_frame (oldRegs regs : Fin 5 → Bool)
    (oldInput input width oldTodo todo oldRow row acc scratch : Word) :
    embedState id framePorts (state oldRegs oldInput width oldTodo oldRow acc scratch)
      (SubexpTaylorFrames.state regs
        {input := input, width := width, todo := todo, output := row}) =
      state regs input width todo row acc scratch := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id framePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    simp only [state, tapes_eq, h0, h3, h8, ite_false]

theorem frame_eval (regs : Fin 5 → Bool) (input width acc : Word) (n : ℕ) :
    ∃ rf, Eval frame (n * (28 * width.length + 33) + 11)
      (state regs input width (List.replicate n true) [] acc [])
      (state rf (input.drop (n * width.length)) width []
        (Encoding.encodeList id (SubexpTaylorFrames.chunks width.length n input)) acc []) := by
  obtain ⟨rf, ht⟩ := SubexpTaylorFrames.program_trace width n input regs
  have he := eval_call_lifted SubexpTaylorFrames.program id framePorts
    (state regs input width (List.replicate n true) [] acc [])
    Function.injective_id framePorts_injective ht
  change Eval frame _
    (embedState id framePorts (state regs input width (List.replicate n true) [] acc [])
      (SubexpTaylorFrames.state regs
        {input := input, width := width, todo := List.replicate n true}))
    (embedState id framePorts (state regs input width (List.replicate n true) [] acc [])
      (SubexpTaylorFrames.state rf
        {input := input.drop (n * width.length), width := width, todo := [],
         output := Encoding.encodeList id
           (SubexpTaylorFrames.chunks width.length n input)})) at he
  rw [embed_frame, embed_frame] at he
  exact ⟨rf, he⟩

def emitPorts : RecordPrograms.Ports 5 11 :=
  ⟨0, 1, 2, 10, 9, by decide, by decide, by decide, by decide⟩

def emit : Code :=
  .seq (.call (StackRoutines.transferProgram 8 10 0 1))
    (.seq (pushConst 9 0 false) (.seq (escape emitPorts) (pushConst 9 0 true)))

theorem emit_eval (regs : Fin 5 → Bool) (input width todo row acc : Word) :
    ∃ rf, Eval emit (8 * row.length + 10)
      (state regs input width todo row acc [])
      (state rf input width todo [] (prependRecord row acc) []) := by
  let a := state regs input width todo row acc []
  let b := afterTransfer a 8 10 0 1
  let c := pushedState 9 0 false b
  let d := escapedState emitPorts c
  let e := pushedState 9 0 true d
  have h1 := SubexpScanPrimitives.transfer_eval a 8 10 0 1 (by decide) (by decide)
  have h2 := pushConst_eval 9 0 false b
  have h3 := escape_eval_state emitPorts c
  have h4 := pushConst_eval 9 0 true d
  have hs : e = state e.regs input width todo [] (prependRecord row acc) [] := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [e, d, c, b, a, state, tapes,
          afterTransfer, emitPorts, StackRoutines.transferStacks, prependRecord,
          frame_eq_escaped]
  have he := h1.seq (h2.seq (h3.seq h4))
  change Eval emit _ a e at he
  rw [hs] at he
  have ha8 : a.stacks 8 = row := rfl
  have hc10 : c.stacks emitPorts.source = row.reverse := by
    simp [c, b, a, afterTransfer, state, tapes, emitPorts,
      StackRoutines.transferStacks]
  refine ⟨e.regs, ?_⟩
  convert he using 1
  · rw [ha8, hc10, List.length_reverse]
    omega

def command : Code := .seq frame emit
def program := compiled command 0 9

theorem chunks_flatten (width : ℕ) (rows : List Word)
    (hrows : ∀ row ∈ rows, row.length = width) :
    SubexpTaylorFrames.chunks width rows.length rows.flatten = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hr : row.length = width := hrows row (by simp)
      have htail : ∀ r ∈ rows, r.length = width := fun r h => hrows r (by simp [h])
      have hp : SubexpExponentProgram.padTake width (row ++ rows.flatten) = row := by
        rw [← hr]
        simp [SubexpExponentProgram.padTake]
      have hd : (row ++ rows.flatten).drop width = rows.flatten := by
        rw [← hr, List.drop_left]
      change SubexpExponentProgram.padTake width (row ++ rows.flatten) ::
        SubexpTaylorFrames.chunks width rows.length ((row ++ rows.flatten).drop width) =
        row :: rows
      rw [hp, hd, ih htail]

theorem flatten_length (width : ℕ) (rows : List Word)
    (hrows : ∀ row ∈ rows, row.length = width) : rows.flatten.length = rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := hrows row (by simp)
      have ht : ∀ r ∈ rows, r.length = width := fun r h => hrows r (by simp [h])
      simp only [List.flatten_cons, List.length_append, hr, ih ht, List.length_cons]
      ring

def rowCost (width : Word) (row : List Word) : ℕ :=
  row.length * (28 * width.length + 33) +
    8 * (Encoding.encodeList id row).length + 21

/-- The physical output is exactly the row format consumed by the
label-indexed factor-packet selector. -/
theorem command_eval (regs : Fin 5 → Bool) (width : Word)
    (row : List Word) (cache : List (List Word))
    (hrow : ∀ word ∈ row, word.length = width.length) :
    ∃ rf, Eval command (rowCost width row)
      (state regs row.flatten width (List.replicate row.length true) []
        (Subexp.FactorPacketCoordinates.cacheBytes cache) [])
      (state rf [] width [] []
        (Subexp.FactorPacketCoordinates.cacheBytes (row :: cache)) []) := by
  obtain ⟨r1, h1⟩ := frame_eval regs row.flatten width
    (Subexp.FactorPacketCoordinates.cacheBytes cache) row.length
  have hlen := flatten_length width.length row hrow
  have hdrop : row.flatten.drop (row.length * width.length) = [] := by
    rw [← hlen]
    exact List.drop_length
  rw [hdrop, chunks_flatten width.length row hrow] at h1
  obtain ⟨r2, h2⟩ := emit_eval r1 [] width [] (Encoding.encodeList id row)
    (Subexp.FactorPacketCoordinates.cacheBytes cache)
  have hcache : prependRecord (Encoding.encodeList id row)
      (Subexp.FactorPacketCoordinates.cacheBytes cache) =
      Subexp.FactorPacketCoordinates.cacheBytes (row :: cache) := rfl
  rw [hcache] at h2
  have hcost : rowCost width row =
      row.length * (28 * width.length + 33) + 11 +
        (8 * (Encoding.encodeList id row).length + 10) := by
    unfold rowCost
    omega
  exact ⟨r2, by simpa only [command, hcost] using h1.seq h2⟩

theorem program_trace (regs : Fin 5 → Bool) (width : Word)
    (row : List Word) (cache : List (List Word))
    (hrow : ∀ word ∈ row, word.length = width.length) :
    ∃ rf, Trace program (rowCost width row + 1)
      ((state regs row.flatten width (List.replicate row.length true) []
        (Subexp.FactorPacketCoordinates.cacheBytes cache) []).withPC (some program.entry))
      ((state rf [] width [] []
        (Subexp.FactorPacketCoordinates.cacheBytes (row :: cache)) []).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval regs width row cache hrow
  exact ⟨rf, compiled_halt_trace he 0 9⟩

end SubexponentialSAT.SubexpLagrangeCacheEncoding

end OAI.Algorithms
