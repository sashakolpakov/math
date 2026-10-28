import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def triplePorts : Fin 15 → Fin 27 := Fin.castAdd 12

theorem triplePorts_injective : Function.Injective triplePorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 27 => x.val) h)

abbrev nativeTriple : Cmd 8 27 := .call (ProgramLinking.liftProgram
  (compiled RingScan.tripleStep 8 0) id triplePorts)

theorem embed_triple (s : Store) (oldRegs regs : Fin 8 → Bool)
    (left source saved : List Bool) :
    embedState id triplePorts (state oldRegs s)
      (RingScan.addState regs s.modulus left [] [] source saved s.count s.width) =
      state regs {s with left := left, source := source, saved := saved} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id triplePorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨10, h.symm⟩
    fin_cases i <;> simp_all [ tapes]

def coefficient (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail c minusOne previous : Word (baseWidth p t)) : Word (baseWidth p t) :=
  (SubexpPreparedQuartic.wordAdd p t M
    (RingScan.tripleProduct p t M tail c minusOne) previous).1

theorem nativeTriple_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (s : Store) (regs : Fin 8 → Bool)
    (tail c minusOne previous : Word (baseWidth p t)) (suffix : List Bool)
    (hmod : s.modulus = M.bits) (hw : s.width.length = baseWidth p t) :
    ∃ n ≤ 18000*(baseWidth p t+1)^2+48*baseWidth p t+43, ∃ rf,
      Eval nativeTriple n
        (state regs {s with left := previous.val, source := tail.val ++ (c.val ++ (minusOne.val ++ suffix)), saved := []})
        (state rf {s with left := (coefficient p t M tail c minusOne previous).val, source := suffix, saved := []}) := by
  obtain ⟨n, hn, rf, he⟩ := RingScan.tripleStep_eval p t M regs tail c minusOne previous
    suffix s.count s.width hw
  have ht := compiled_halt_trace he 8 0
  let initial := {s with left := previous.val, source := tail.val ++ (c.val ++ (minusOne.val ++ suffix)), saved := []}
  have h := eval_call_lifted (compiled RingScan.tripleStep 8 0) id triplePorts
    (state regs initial) Function.injective_id triplePorts_injective ht
  refine ⟨n+1, by omega, rf, ?_⟩
  simpa only [nativeTriple, ← hmod, embed_triple, initial, coefficient] using h

/-- Assemble a triple from saved tail, next polynomial coefficient, and -1;
perform the native multiply-add; retain the last output and advance a's shift. -/
abbrev coefficientStep : Cmd 8 27 :=
  .seq (copy 17 9) (.seq (load 16 9) (.seq (copy 18 9)
    (.seq nativeTriple (.seq (clear 19) (.seq (copy 0 19)
      (.seq (transfer 0 20) (load 15 0)))))))


theorem coefficientStep_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (s : Store) (regs : Fin 8 → Bool)
    (tail c minusOne previous current : Word (baseWidth p t)) (ct avtail : List Bool)
    (hmod : s.modulus = M.bits) (hw : s.width.length = baseWidth p t)
    (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ 18000*(baseWidth p t+1)^2+102*baseWidth p t+88, ∃ rf,
      Eval coefficientStep n
        (state regs {s with left := previous.val, source := [], saved := [], vector := current.val ++ avtail, coefficients := c.val ++ ct, tail := tail.val, minusOne := minusOne.val})
        (state rf {s with left := current.val, source := [], saved := [], vector := avtail, coefficients := ct, tail := tail.val, minusOne := minusOne.val, newTail := (coefficient p t M tail c minusOne previous).val, output := (coefficient p t M tail c minusOne previous).val.reverse ++ s.output}) := by
  let z := coefficient p t M tail c minusOne previous
  let s0 := {s with left := previous.val, source := [], saved := [], vector := current.val ++ avtail, coefficients := c.val ++ ct, tail := tail.val, minusOne := minusOne.val}
  let s1 := {s0 with source := minusOne.val}
  let s2 := {s1 with source := c.val ++ minusOne.val, coefficients := ct}
  let s3 := {s2 with source := tail.val ++ (c.val ++ minusOne.val)}
  let s4 := {s3 with left := z.val, source := []}
  let s5 := {s4 with newTail := []}
  let s6 := {s5 with newTail := z.val}
  let s7 := {s6 with left := [], output := z.val.reverse ++ s.output}
  let s8 := {s7 with left := current.val, vector := avtail}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s0 s1 regs 17 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s0, s1])
  have h2 := load_store_eval s1 s2 rr 16 9 (by decide) c.val ct (by rfl)
    (hw.trans c.property.symm) (by
      funext i; fin_cases i <;> simp [tapes, s2, s1, s0])
  have h3 := copy_store_eval s2 s3 rr 18 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s3, s2, s1, s0])
  obtain ⟨n, hn, rf, h4⟩ := nativeTriple_eval p t M s3 rr tail c minusOne previous [] hmod hw
  have hh4 : Eval nativeTriple n (state rr s3) (state rf s4) := by
    simpa only [s4, s3, s2, s1, s0, z, List.append_nil] using h4
  have h5 := clear_store_eval s4 s5 rf 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s5, s4])
  let rg := readRegs rf 1 3 none
  have h6 := copy_store_eval s5 s6 rg 0 19 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s6, s5, s4])
  have h7 := transfer_store_eval s6 s7 rg 0 20 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s7, s6, s5, s4, s3, s2, s1, s0])
  have h8 := load_store_eval s7 s8 rg 15 0 (by decide) current.val avtail (by rfl)
    (hw.trans current.property.symm) (by
      funext i; fin_cases i <;> simp [tapes, s8, s7])
  simp only [rr, rg, readRegs_reset] at h2 h3 h6 h7 h8
  have he := h1.seq (h2.seq (h3.seq (hh4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨_, ?_, rg, he⟩
  simp [s0, s1, s2, s3, s4, s5, s6, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
