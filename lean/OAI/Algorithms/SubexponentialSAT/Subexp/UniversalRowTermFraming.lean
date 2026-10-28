import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Physical framing of a gathered correction term and the final row. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermFraming

open BitProgram StructuredCalls

abbrev Data := State 8 32
abbrev Word := List Bool

abbrev term : Cmd 8 32 :=
  .seq (MatrixProgramSupport.emitFrame 20 21 23 (by decide))
    (.seq (MatrixProgramSupport.emitFrame 19 21 23 (by decide))
      (.seq (MatrixProgramSupport.emitFrame 21 31 23 (by decide))
        (TupleProgram.pushConst 31 0 true)))

def termCost (value inverse factorBytes : Word) : ℕ :=
  24 * (value.length + inverse.length) + 8 * factorBytes.length + 42

theorem term_eval (a : Data) (value inverse : Word)
    (fs : List (UniversalRowProgram.Factor Word))
    (hv : a.stacks 19 = value) (hi : a.stacks 20 = inverse)
    (hf : a.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor fs)
    (h23 : a.stacks 23 = []) :
    ∃ b : Data,
      Eval term (termCost value inverse (Encoding.encodeList UniversalRowProgram.encodeFactor fs)) a b ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 19 []) 20 []) 21 []) 31
        (true :: (Encoding.frame (UniversalRowProgram.encodeTerm ⟨value, inverse, fs⟩) ++
          a.stacks 31)) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 20 21 23
    (by decide) (by decide) (by decide) a h23
  obtain ⟨c, hc, hcs⟩ := MatrixProgramSupport.emitFrame_eval 19 21 23
    (by decide) (by decide) (by decide) b (by rw [hbs]; simpa using h23)
  obtain ⟨d, hd, hds⟩ := MatrixProgramSupport.emitFrame_eval 21 31 23
    (by decide) (by decide) (by decide) c (by rw [hcs, hbs]; simpa using h23)
  let e := TupleProgram.pushedState (31 : Fin 32) (0 : Fin 8) true d
  have he := TupleProgram.pushConst_eval (31 : Fin 32) (0 : Fin 8) true d
  refine ⟨e, ?_, ?_⟩
  · have ht := hb.seq (hc.seq (hd.seq he))
    convert ht using 1
    simp [termCost, hcs, hbs, hv, hi, hf, Encoding.length_frame]
    ring
  · simp only [e ]
    rw [hds, hcs, hbs]
    funext j
    by_cases h19 : j = 19 <;> by_cases h20 : j = 20 <;>
      by_cases h21 : j = 21 <;> by_cases h31 : j = 31 <;>
        simp_all [ UniversalRowProgram.encodeTerm, List.append_assoc]

abbrev row : Cmd 8 32 := MatrixProgramSupport.emitFrame 18 31 23 (by decide)

theorem row_eval (a : Data) (delta : Word)
    (ts : List (UniversalRowProgram.Term Word))
    (hd : a.stacks 18 = delta)
    (ht : a.stacks 31 = Encoding.encodeList UniversalRowProgram.encodeTerm ts)
    (h23 : a.stacks 23 = []) :
    ∃ b : Data, Eval row (8 * delta.length + 8) a b ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.encodeRow ⟨delta, ts⟩) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 18 31 23
    (by decide) (by decide) (by decide) a h23
  refine ⟨b, ?_, ?_⟩
  · simpa [row, hd] using hb
  · simpa [hd, ht, UniversalRowProgram.encodeRow] using hbs

end SubexponentialSAT.Subexp.UniversalRowTermFraming

end OAI.Algorithms
