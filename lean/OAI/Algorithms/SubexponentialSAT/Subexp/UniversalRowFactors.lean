import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! Fixed array reads and framing for one interpolation factor. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactors

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)

abbrev readAt (ports : Equiv.Perm (Fin 32)) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram
    (compiled (UniversalRowGather.readIndex .value) 0 0) id ports)

theorem readAt_eval (ports : Equiv.Perm (Fin 32)) (rows : List Word)
    (width index : Word) (a : Data)
    (ha : a.stacks (ports 24) = rows.flatten)
    (hw : a.stacks (ports 29) = width) (hi : a.stacks (ports 16) = index)
    (hindex : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (ports 19) = []) (h2 : a.stacks (ports 2) = [])
    (h4 : a.stacks (ports 4) = []) (h5 : a.stacks (ports 5) = [])
    (h6 : a.stacks (ports 6) = []) (h7 : a.stacks (ports 7) = [])
    (h15 : a.stacks (ports 15) = []) :
    Eval (readAt ports)
      (index.length * (14 * width.length + 17) + 15 * width.length + 22)
      a ⟨readRegs a.regs 0 1 none, Function.update a.stacks (ports 19) (rows.getD index.length [])⟩ := by
  let inner : Data := ⟨a.regs, a.stacks ∘ ports⟩
  have ht := UniversalRowGather.readIndex_eval .value rows width index inner
    ha hw hi hindex hrows hout h2 h4 h5 h6 h7 h15
  have hin : embedState id ports a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports.injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hend : embedState id ports a
      (UniversalRowGather.result .value inner (rows.getD index.length [])) =
      (⟨readRegs a.regs 0 1 none,
        Function.update a.stacks (ports 19) (rows.getD index.length [])⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id ports.injective
    · intros; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      simp [UniversalRowGather.result, UniversalRowGather.outputPort, inner,
        Function.update_apply, ports.injective.eq_iff]
    · intro i hi; exact False.elim (hi ⟨ports.symm i, ports.apply_symm_apply i⟩)
  have he := eval_call_lifted (compiled (UniversalRowGather.readIndex .value) 0 0)
    id ports a Function.injective_id ports.injective (compiled_halt_trace ht 0 0)
  simpa only [hin, hend, readAt, Nat.add_assoc] using he

def differencePorts : Equiv.Perm (Fin 32) :=
  (Equiv.swap 0 24).trans ((Equiv.swap 1 19).trans (Equiv.swap 9 16))

def negativePorts : Equiv.Perm (Fin 32) :=
  (Equiv.swap 24 26).trans ((Equiv.swap 12 19).trans (Equiv.swap 9 16))

abbrev readFactor : Cmd 8 32 := .seq (readAt differencePorts) (readAt negativePorts)

theorem readFactor_eval (differences negatives : List Word) (width index : Word) (a : Data)
    (hd : a.stacks 0 = differences.flatten) (hn : a.stacks 26 = negatives.flatten)
    (hw : a.stacks 29 = width) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval readFactor (2 * index.length * (14 * width.length + 17) + 30 * width.length + 44)
      a ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 1 (differences.getD index.length []))
          12 (negatives.getD index.length [])⟩ := by
  have hp : differencePorts 24 = 0 ∧ differencePorts 19 = 1 ∧ differencePorts 16 = 9 ∧
      differencePorts 29 = 29 ∧ differencePorts 2 = 2 ∧ differencePorts 4 = 4 ∧
      differencePorts 5 = 5 ∧ differencePorts 6 = 6 ∧ differencePorts 7 = 7 ∧
      differencePorts 15 = 15 := by decide
  have hq : negativePorts 24 = 26 ∧ negativePorts 19 = 12 ∧ negativePorts 16 = 9 ∧
      negativePorts 29 = 29 ∧ negativePorts 2 = 2 ∧ negativePorts 4 = 4 ∧
      negativePorts 5 = 5 ∧ negativePorts 6 = 6 ∧ negativePorts 7 = 7 ∧
      negativePorts 15 = 15 := by decide
  let b : Data := ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 1 (differences.getD index.length [])⟩
  have hfirst := readAt_eval differencePorts differences width index a
    (by simpa [hp.1] using hd) (by simpa [hp.2.2.2.1] using hw)
    (by simpa [hp.2.2.1] using hi) hid hds
    (by simpa [hp.2.1] using h1)
    (by simpa [hp.2.2.2.2.1] using h2)
    (by simpa [hp.2.2.2.2.2.1] using h4)
    (by simpa [hp.2.2.2.2.2.2.1] using h5)
    (by simpa [hp.2.2.2.2.2.2.2.1] using h6)
    (by simpa [hp.2.2.2.2.2.2.2.2.1] using h7)
    (by simpa [hp.2.2.2.2.2.2.2.2.2] using h15)
  have hsecond := readAt_eval negativePorts negatives width index b
    (by simpa [b, hq.1] using hn) (by simpa [b, hq.2.2.2.1] using hw)
    (by simpa [b, hq.2.2.1] using hi) hin hns
    (by simpa [b, hq.2.1] using h12)
    (by simpa [b, hq.2.2.2.2.1] using h2)
    (by simpa [b, hq.2.2.2.2.2.1] using h4)
    (by simpa [b, hq.2.2.2.2.2.2.1] using h5)
    (by simpa [b, hq.2.2.2.2.2.2.2.1] using h6)
    (by simpa [b, hq.2.2.2.2.2.2.2.2.1] using h7)
    (by simpa [b, hq.2.2.2.2.2.2.2.2.2] using h15)
  rw [hp.2.1] at hfirst
  rw [hq.2.1] at hsecond
  have ht := hfirst.seq hsecond
  convert ht using 1
  · ring
  · simp [b, StackRoutines.readRegs_reset]

/-- Prepend one complete factor record from its two raw scalar payloads.
The output is a record-list accumulator; its existing suffix is preserved. -/
abbrev emitFactor : Cmd 8 32 :=
  .seq (MatrixProgramSupport.emitFrame 12 22 23 (by decide))
    (.seq (MatrixProgramSupport.emitFrame 1 22 23 (by decide))
      (.seq (MatrixProgramSupport.emitFrame 22 21 23 (by decide))
        (TupleProgram.pushConst 21 0 true)))

theorem emitFactor_eval (a : Data) (inverse negative : Word)
    (hinv : a.stacks 1 = inverse) (hneg : a.stacks 12 = negative)
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ b : Data, Eval emitFactor (24 * (inverse.length + negative.length) + 42) a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks 1 []) 12 []) 21
        (true :: (Encoding.frame (UniversalRowProgram.encodeFactor ⟨inverse, negative⟩) ++ a.stacks 21)) := by
  obtain ⟨b, hb, hbs⟩ := MatrixProgramSupport.emitFrame_eval 12 22 23
    (by decide) (by decide) (by decide) a h23
  obtain ⟨c, hc, hcs⟩ := MatrixProgramSupport.emitFrame_eval 1 22 23
    (by decide) (by decide) (by decide) b (by rw [hbs]; simpa using h23)
  obtain ⟨d, hd, hds⟩ := MatrixProgramSupport.emitFrame_eval 22 21 23
    (by decide) (by decide) (by decide) c (by rw [hcs, hbs]; simpa using h23)
  let e := TupleProgram.pushedState (21 : Fin 32) (0 : Fin 8) true d
  have he := TupleProgram.pushConst_eval (21 : Fin 32) (0 : Fin 8) true d
  refine ⟨e, ?_, ?_⟩
  · have run := hb.seq (hc.seq (hd.seq he))
    convert run using 1
    simp [hbs, hcs, hinv, hneg, h22, Encoding.length_frame]
    ring
  · simp only [e ]
    rw [hds, hcs, hbs]
    funext j
    by_cases h1 : j = 1 <;> by_cases h12 : j = 12 <;>
      by_cases h21 : j = 21 <;> by_cases h22' : j = 22 <;>
      simp_all [Function.update_apply, UniversalRowProgram.encodeFactor ]

end SubexponentialSAT.Subexp.UniversalRowFactors

end OAI.Algorithms
