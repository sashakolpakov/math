import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramPrefixAlgebra
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Framed invocation of the fixed three-stack prefix and dot programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def replaceThree {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) : Fin S → List Bool :=
  Function.update (Function.update (Function.update stk (ports 0) a) (ports 1) b) (ports 2) c

theorem replaceThree_at {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) (i : Fin 3) :
    replaceThree ports a b c stk (ports i) = ![a, b, c] i := by
  fin_cases i <;> simp [replaceThree, ports.injective.eq_iff]

theorem replaceThree_frame {S : ℕ} (ports : Fin 3 ↪ Fin S) (a b c : List Bool)
    (stk : Fin S → List Bool) (i : Fin S) (hi : ¬∃ j, ports j = i) :
    replaceThree ports a b c stk i = stk i := by
  have h0 : i ≠ ports 0 := fun h => hi ⟨0, h.symm⟩
  have h1 : i ≠ ports 1 := fun h => hi ⟨1, h.symm⟩
  have h2 : i ≠ ports 2 := fun h => hi ⟨2, h.symm⟩
  simp [replaceThree, h0, h1, h2]

noncomputable def afterThree {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (rf : Fin r → Bool) (a b c : List Bool) (d : State R S) : State R S :=
  ⟨Function.extend regs rf d.regs, replaceThree ports a b c d.stacks⟩

theorem three_embed {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (rf : Fin r → Bool) (a b c : List Bool) (d : State R S) :
    embedState regs ports d ⟨rf, ![a, b, c]⟩ = afterThree regs ports rf a b c d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i
    exact regs.injective.extend_apply _ _ _
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i
    exact replaceThree_at ports a b c d.stacks i
  · intro i hi
    exact replaceThree_frame ports a b c d.stacks i hi

theorem three_initial {r R S : ℕ} (regs : Fin r ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (a b c : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = a) (hb : d.stacks (ports 1) = b)
    (hc : d.stacks (ports 2) = c) :
    embedState regs ports d ⟨fun i => d.regs (regs i), ![a, b, c]⟩ = d := by
  apply embedState_eq_of_ports regs ports d _ _ regs.injective ports.injective
  · intro i; rfl
  · intros; rfl
  · intro i
    fin_cases i <;> assumption
  · intros; rfl

abbrev prefixCall {R S : ℕ} (regs : Fin 6 ↪ Fin R) (ports : Fin 3 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram prefixReverseProgram regs ports)

theorem prefixCall_eval {R S : ℕ} (regs : Fin 6 ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (as : List IrreducibleSearch.F) (count output : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = coefficientArray as)
    (hb : d.stacks (ports 1) = count) (hc : d.stacks (ports 2) = output) :
    ∃ rf, Eval (prefixCall regs ports) (7 * count.length + 3) d
      (afterThree regs ports rf (coefficientArray (as.drop count.length)) []
        (coefficientArray (paddedPrefix count.length as).reverse ++ output) d) := by
  obtain ⟨rf, he⟩ := prefixReverse_trace as count output (fun i => d.regs (regs i))
  have ht := eval_call_lifted prefixReverseProgram regs ports d regs.injective ports.injective
    (a := ⟨fun i => d.regs (regs i), ![coefficientArray as, count, output]⟩)
    (b := ⟨rf, ![coefficientArray (as.drop count.length), [],
      coefficientArray (paddedPrefix count.length as).reverse ++ output]⟩) he
  rw [three_initial regs ports _ _ _ d ha hb hc, three_embed] at ht
  exact ⟨rf, ht⟩

abbrev dotCall {R S : ℕ} (regs : Fin 8 ↪ Fin R) (ports : Fin 3 ↪ Fin S) : Cmd R S :=
  .call (ProgramLinking.liftProgram dotProgram regs ports)

theorem dotCall_eval {R S : ℕ} (regs : Fin 8 ↪ Fin R) (ports : Fin 3 ↪ Fin S)
    (as bs : List IrreducibleSearch.F) (hlen : as.length = bs.length)
    (output : List Bool) (d : State R S)
    (ha : d.stacks (ports 0) = coefficientArray as)
    (hb : d.stacks (ports 1) = coefficientArray bs) (hc : d.stacks (ports 2) = output) :
    ∃ rf, Eval (dotCall regs ports) (15 * as.length + 7) d
      (afterThree regs ports rf [] []
        (coefficientWord ((List.zipWith (· * ·) as bs).sum) ++ output) d) := by
  obtain ⟨rf, he⟩ := dotProgram_run as bs hlen (fun i => d.regs (regs i)) output
  have ht := eval_call_lifted dotProgram regs ports d regs.injective ports.injective he
  simp only [dotInput] at ht
  rw [three_initial regs ports _ _ _ d ha hb hc, three_embed] at ht
  exact ⟨rf, ht⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
