import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Select one fixed-width framed scalar from the coefficient stream using
the actual persistent array reader, then decode its frame. The index and
frame width are supplied as unary runtime data. -/

namespace SubexponentialSAT.Subexp.MatrixWordSelectProgram

open BitProgram StructuredCalls StackRoutines MatrixProgramSupport

abbrev Data := State 8 16

def ports : Fin 8 → Fin 16 := ![12, 13, 15, 10, 2, 3, 4, 6]

theorem ports_injective : Function.Injective ports := by decide

abbrev lookup : Cmd 8 16 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1) id ports)

abbrev lookupOutput (a : Data) (bits : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 15 []) 13 (Encoding.frame bits)⟩

private theorem frames_flatten (xs : List (List Bool)) :
    (xs.map Encoding.frame).flatten = words xs := by
  induction xs with
  | nil => rfl
  | cons row rows ih => simp [words, ih]

theorem lookup_eval (a : Data) (before : List (List Bool)) (bits tail : List Bool) (B : ℕ)
    (hrows : ∀ row ∈ before, row.length = B) (hb : bits.length = B)
    (hsource : a.stacks 12 = words before ++ (Encoding.frame bits ++ tail))
    (hindex : (a.stacks 15).length = before.length)
    (hwidth : (a.stacks 10).length = 2 * B + 1)
    (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) (h13 : a.stacks 13 = []) :
    Eval lookup (before.length * (14 * (2 * B + 1) + 10) + 15 * (2 * B + 1) + 16)
      a (lookupOutput a bits) := by
  let inner : State 8 8 := ⟨a.regs, fun j => a.stacks (ports j)⟩
  have hshape : inner.stacks 0 = (before.map Encoding.frame).flatten ++
      (Encoding.frame bits ++ tail) := by simpa [inner, ports, frames_flatten] using hsource
  have hlength : ∀ row ∈ before.map Encoding.frame, row.length = (a.stacks 10).length := by
    intro row hr
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
    rw [Encoding.length_frame, hrows r hmem, hwidth]
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    (before.map Encoding.frame) (Encoding.frame bits) tail (a.stacks 10) (a.stacks 15)
    inner.regs inner.stacks hshape rfl rfl
    (by simpa using hindex) hlength
    (by simp [Encoding.length_frame, hb, hwidth]) h2 h3 h4 h6
  have hstart : embedState id ports a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j; rfl
    · intros; rfl
  have hfinish : embedState id ports a
      ⟨readRegs inner.regs 0 1 none, ArrayUpdatePrograms.readStacks (Encoding.frame bits) inner.stacks⟩ =
      lookupOutput a bits := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j
      fin_cases j <;> simp [ inner, ports, ArrayUpdatePrograms.readStacks, h13]
    · intro j hj
      have h15 : j ≠ 15 := fun h => hj ⟨2, h.symm⟩
      have h13' : j ≠ 13 := fun h => hj ⟨1, h.symm⟩
      simp [ h15, h13']
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id ports a Function.injective_id ports_injective
    (a := inner)
    (b := ⟨readRegs inner.regs 0 1 none, ArrayUpdatePrograms.readStacks (Encoding.frame bits) inner.stacks⟩) ht
  rw [hstart, hfinish] at he
  simpa only [lookup, List.length_map, hwidth] using he

abbrev command : Cmd 8 16 :=
  .seq lookup (readWord 13 0 9 (by decide))

def budget (A B : ℕ) : ℕ :=
  A * (14 * (2 * B + 1) + 10) + 15 * (2 * B + 1) + 16 + 9 * B + 7

/-- The selected scalar is returned on stack 0; the coefficient array and
frame-width template are preserved, and the index is consumed. -/
theorem command_eval (a : Data) (before : List (List Bool)) (bits tail : List Bool) (B : ℕ)
    (hrows : ∀ row ∈ before, row.length = B) (hb : bits.length = B)
    (hsource : a.stacks 12 = words before ++ (Encoding.frame bits ++ tail))
    (hindex : (a.stacks 15).length = before.length)
    (hwidth : (a.stacks 10).length = 2 * B + 1)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) (h9 : a.stacks 9 = []) (h13 : a.stacks 13 = []) :
    ∃ e : Data, Eval command (budget before.length B) a e ∧
      e.stacks = Function.update (Function.update a.stacks 15 []) 0 bits := by
  have hl := lookup_eval a before bits tail B hrows hb hsource hindex hwidth h2 h3 h4 h6 h13
  obtain ⟨e, he, hse⟩ := readWord_eval (13 : Fin 16) 0 9
    (by decide) (by decide) (by decide) (lookupOutput a bits) bits []
    (by simp []) (by simpa [lookupOutput] using h0)
    (by simpa [lookupOutput] using h9)
  refine ⟨e, ?_, ?_⟩
  · simpa only [command, budget, hb, Nat.add_assoc] using hl.seq he
  · rw [hse]
    funext j
    fin_cases j <;> simp [ h13]

def program := compiled command 12 0

theorem program_runsIn (a : Data) (before : List (List Bool)) (bits tail : List Bool) (B : ℕ)
    (hrows : ∀ row ∈ before, row.length = B) (hb : bits.length = B)
    (hsource : a.stacks 12 = words before ++ (Encoding.frame bits ++ tail))
    (hindex : (a.stacks 15).length = before.length)
    (hwidth : (a.stacks 10).length = 2 * B + 1)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) (h9 : a.stacks 9 = []) (h13 : a.stacks 13 = []) :
    ∃ e : Data, RunsIn program (budget before.length B + 1)
      (a.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update a.stacks 15 []) 0 bits := by
  obtain ⟨e, he, hs⟩ := command_eval a before bits tail B hrows hb hsource hindex hwidth
    h0 h2 h3 h4 h6 h9 h13
  exact ⟨e, ⟨_, le_rfl, compiled_halt_trace he 12 0⟩, hs⟩

end SubexponentialSAT.Subexp.MatrixWordSelectProgram

end OAI.Algorithms
