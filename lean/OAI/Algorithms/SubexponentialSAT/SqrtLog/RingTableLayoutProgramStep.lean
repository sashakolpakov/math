import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def wordAt (rows : List (List Bool)) (i : ℕ) : List Bool := rows[i]!

theorem wordAt_length (rows : List (List Bool)) (i B : ℕ)
    (hi : i < rows.length) (hw : ∀ row ∈ rows, row.length = B) :
    (wordAt rows i).length = B := by
  simpa [wordAt, getElem!_pos, hi] using hw rows[i] (List.getElem_mem hi)

theorem readAt_eval (d : Data) (rows : List (List Bool)) (i : ℕ)
    (hp : d.stacks 0 = rows.flatten) (hi : (d.stacks 5).length = i)
    (hb : i < rows.length) (hw : ∀ row ∈ rows, row.length = (d.stacks 2).length)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    Eval read (i * (14 * (d.stacks 2).length + 10) + 15 * (d.stacks 2).length + 16)
      d (afterRead d (wordAt rows i)) := by
  have hsplit : rows = rows.take i ++ rows[i] :: rows.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hb]
    exact (List.take_append_drop i rows).symm
  have hflat : rows.flatten = (rows.take i).flatten ++
      (wordAt rows i ++ (rows.drop (i+1)).flatten) := by
    simpa only [wordAt, getElem!_pos, hb, List.flatten_append, List.flatten_cons]
      using congrArg List.flatten hsplit
  have hlen : (rows.take i).length = i := by simp [Nat.min_eq_left (Nat.le_of_lt hb)]
  have ht := read_eval d (rows.take i) (wordAt rows i) (rows.drop (i+1)).flatten
    (hp.trans hflat) (hi.trans hlen.symm)
    (by intro row hr; exact hw row (List.mem_of_mem_take hr))
    (wordAt_length rows i _ hb hw) h6 h7 h8 h9
  simpa only [hlen] using ht

/-- Read one scalar at the current flat-record offset, prepend its reversed
bits to the output accumulator, and advance the offset by one vector. -/
abbrev emit : Cmd 2 18 :=
  .seq (copy 16 5) (.seq read (.seq (transfer 4 17) (copy 1 16)))

theorem emit_eval (s : Store) (regs : Fin 2 → Bool) (rows : List (List Bool))
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hb : s.ji.length < rows.length) (hword : s.word = []) (hindex : s.index = []) :
    ∃ rf, Eval emit
      (s.ji.length * (14 * s.width.length + 17) +
        18 * s.width.length + 7 * s.degree.length + 29)
      (state regs s)
      (state rf {s with
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev}) := by
  let d := state regs s
  let a := afterCopy d 16 5
  let b := afterRead a (wordAt rows s.ji.length)
  let c := afterTransfer b 4 17
  have h1 := copy_eval d 16 5 (by decide) (by decide) (by decide) (by rfl)
  have h2 := readAt_eval a rows s.ji.length
    (by simpa [a, d, afterCopy, copyStacks, state, tapes] using hp)
    (by simp [a, d, afterCopy, copyStacks, state, tapes, hindex]) hb
    (by simpa [a, d, afterCopy, copyStacks, state, tapes] using hw)
    (by rfl) (by rfl) (by rfl) (by rfl)
  have h3 := transfer_eval b 4 17 (by decide)
  have h4 := copy_eval c 1 16 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy c 1 16 =
      state (afterCopy c 1 16).regs {s with
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [c, b, a, d, afterCopy, afterRead, afterTransfer,
          copyStacks, transferStacks, state, tapes, hword, hindex]
  refine ⟨(afterCopy c 1 16).regs, ?_⟩
  rw [← hf]
  have hwl := wordAt_length rows s.ji.length s.width.length hb hw
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  simp [c, b, a, d, afterCopy, afterRead, afterTransfer,
    copyStacks, transferStacks, state, tapes, hword, hindex, hwl]
  ring

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
