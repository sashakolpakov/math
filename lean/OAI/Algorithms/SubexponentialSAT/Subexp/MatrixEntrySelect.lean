import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryFrames
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientPascalProgram

namespace OAI.Algorithms

/-! Framed selection and sign application inside the actual entry workspace. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding

theorem signedStacks_injective : Function.Injective signedStacks := by decide

def signedResult (a : Data) (out : Fin 9 → Bool) (p : ℕ) (x : ZMod p) : Data :=
  ⟨out, Function.update (Function.update a.stacks 34 []) 0 (word p x)⟩

theorem signedWord_eval (p : ℕ) [Fact p.Prime] (a : Data) (x : ZMod p) (count : List Bool)
    (hlocal : ∀ j, a.stacks (signedStacks j) =
      (MatrixSignedWordProgram.state p a.regs x count).stacks j) :
    ∃ n ≤ 6073 * (width p + 1)^2 + 3 * count.length + 7, ∃ out,
      Eval signedWord n a (signedResult a out p ((-1 : ZMod p)^count.length * x)) := by
  obtain ⟨out, n, hn, ht⟩ := MatrixSignedWordProgram.program_runsIn p a.regs x count
  have hstart : embedState id signedStacks a (MatrixSignedWordProgram.state p a.regs x count) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id signedStacks_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · exact hlocal
    · intros; rfl
  have hfinish : embedState id signedStacks a
      (MatrixSignedWordProgram.state p out ((-1 : ZMod p)^count.length * x) []) =
      signedResult a out p ((-1 : ZMod p)^count.length * x) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id signedStacks_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j
      have hj := hlocal j
      fin_cases j <;> simp_all [signedResult, signedStacks, MatrixSignedWordProgram.state]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h34 : j ≠ 34 := fun h => hj ⟨9, h.symm⟩
      simp [signedResult, h0, h34]
  have he := eval_call_lifted MatrixSignedWordProgram.program id signedStacks a
    Function.injective_id signedStacks_injective ht
  rw [hstart, hfinish] at he
  exact ⟨n, hn, out, he⟩

theorem valueWords_split (p : ℕ) [Fact p.Prime] (ys : List (ZMod p)) (A : ℕ)
    (hA : A < ys.length) :
    CoefficientPascalProgram.valueWords p ys =
      MatrixProgramSupport.words ((ys.take A).map (word p)) ++
        (Encoding.frame (word p (ys.getD A 0)) ++
          CoefficientPascalProgram.valueWords p (ys.drop (A + 1))) := by
  have hsplit := List.take_append_drop A ys
  rw [List.drop_eq_getElem_cons hA] at hsplit
  have hget : ys.getD A 0 = ys[A] := List.getD_eq_getElem _ _ hA
  have he : ys = ys.take A ++ ys.getD A 0 :: ys.drop (A + 1) := by
    simpa only [hget] using hsplit.symm
  conv_lhs => rw [he, CoefficientPascalProgram.valueWords_append,
    CoefficientPascalProgram.valueWords_cons]
  rfl

/-- Selection invokes the fixed persistent array reader and the fixed frame
decoder. The full working coefficient stream is preserved. -/
theorem selectWord_eval (p : ℕ) [Fact p.Prime] (a : Data) (ys : List (ZMod p)) (A : ℕ)
    (hA : A < ys.length)
    (hsource : a.stacks 12 = CoefficientPascalProgram.valueWords p ys)
    (hindex : (a.stacks 15).length = A)
    (hwidth : (a.stacks 10).length = 2 * width p + 1)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) (h9 : a.stacks 9 = [])
    (h13 : a.stacks 13 = []) :
    ∃ n ≤ MatrixWordSelectProgram.budget A (width p) + 1, ∃ b : Data,
      Eval (callLow MatrixWordSelectProgram.program (by decide)) n a b ∧
        b.stacks = Function.update (Function.update a.stacks 15 []) 0
          (word p (ys.getD A 0)) := by
  let inner := project (by decide : 16 ≤ 37) a
  obtain ⟨e, he, hs⟩ := MatrixWordSelectProgram.program_runsIn inner
    ((ys.take A).map (word p)) (word p (ys.getD A 0))
    (CoefficientPascalProgram.valueWords p (ys.drop (A + 1))) (width p)
    (by intro row hrow; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hrow; simp)
    (by simp)
    (by simpa [inner, project, hsource] using valueWords_split p ys A hA)
    (by simpa [inner, project, Nat.min_eq_left hA.le] using hindex)
    hwidth h0 h2 h3 h4 h6 h9 h13
  obtain ⟨n, hn, ht⟩ := callLow_runsIn MatrixWordSelectProgram.program (by decide) a e he
  refine ⟨n, by simpa [List.length_take, Nat.min_eq_left hA.le] using hn,
    install a e, ht, ?_⟩
  funext j
  simp only [install]
  by_cases hj : j.val < 16
  · rw [dite_eq_left hj, hs]
    simp only [inner, project]
    by_cases h15 : j = 15
    · subst j; rfl
    by_cases hzero : j = 0
    · subst j; rfl
    have h15' : (⟨j.val, hj⟩ : Fin 16) ≠ 15 := by
      intro h; exact h15 (Fin.ext (congrArg (fun k : Fin 16 => k.val) h))
    have hz' : (⟨j.val, hj⟩ : Fin 16) ≠ 0 := by
      intro h; exact hzero (Fin.ext (congrArg (fun k : Fin 16 => k.val) h))
    simp [h15, hzero, h15', hz']
  · rw [dite_eq_right hj]
    have h15 : j ≠ 15 := by intro h; subst j; exact hj (by decide)
    have hz : j ≠ 0 := by intro h; subst j; exact hj (by decide)
    simp [h15, hz]

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
