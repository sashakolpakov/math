import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 17

abbrev smallRegs : Fin 5 → Fin 8 := Fin.castAdd 3
abbrev smallStacks : Fin 13 → Fin 17 := Fin.castAdd 4

theorem smallRegs_injective : Function.Injective smallRegs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 8 => k.val) h

theorem smallStacks_injective : Function.Injective smallStacks := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 17 => k.val) h

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11

abbrev equality : Cmd 8 17 := .call
  (ProgramLinking.liftProgram equalityInner smallRegs smallStacks)

abbrev compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (compared a (decide (a.stacks 1 = a.stacks 12))) := by
  let x : State 5 13 := ⟨fun j => a.regs (smallRegs j), fun j => a.stacks (smallStacks j)⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  have hstart : embedState smallRegs smallStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective smallStacks_injective
    · intro i; rfl
    · intros; rfl
    · intro i; rfl
    · intros; rfl
  have hfinish : embedState smallRegs smallStacks a
      (CollisionStreamProgram.sealed x (decide (x.stacks 1 = x.stacks 12))) =
      compared a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective smallStacks_injective
    · intro i; fin_cases i <;> norm_num [compared, CollisionStreamProgram.sealed, smallRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h
        exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro i; fin_cases i <;> simp [ CollisionStreamProgram.sealed, x, smallStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityInner smallRegs smallStacks a
    smallRegs_injective smallStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · change n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 at hn
    omega
  · simpa only [hstart, hfinish, equality] using he

abbrev copy (src dst : Fin 17) : Cmd 8 17 := .call (copyProgram src dst 0 0 1)
abbrev copied (a : Data) (src dst : Fin 17) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 17) (hsd : src ≠ dst)
    (hs0 : src ≠ 0) (h0d : (0 : Fin 17) ≠ dst) (h0 : a.stacks 0 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 0 (0 : Fin 8) 1 hsd hs0 h0d (by decide) a h0

def firstSource (swapped : Bool) : Fin 17 := if swapped then 13 else 14
def secondSource (swapped : Bool) : Fin 17 := if swapped then 14 else 13

abbrev prepare (swapped : Bool) : Cmd 8 17 :=
  .seq (copy (firstSource swapped) 1) (.seq (copy (secondSource swapped) 1)
    (.seq (copy 16 12) (copy 15 12)))

def leftWord (a : Data) (swapped : Bool) : List Bool :=
  if swapped then a.stacks 14 ++ a.stacks 13 else a.stacks 13 ++ a.stacks 14

def volume (a : Data) : ℕ :=
  (a.stacks 13).length + (a.stacks 14).length + (a.stacks 15).length + (a.stacks 16).length

abbrev prepared (a : Data) (swapped : Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 1 (leftWord a swapped))
      12 (a.stacks 15 ++ a.stacks 16)⟩

theorem prepare_eval (a : Data) (swapped : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = []) :
    Eval (prepare swapped) (7 * volume a + 20) a (prepared a swapped) := by
  let a1 := copied a (firstSource swapped) 1
  let a2 := copied a1 (secondSource swapped) 1
  let a3 := copied a2 16 12
  let a4 := copied a3 15 12
  have t0 := copy_eval a (firstSource swapped) 1
    (by cases swapped <;> decide) (by cases swapped <;> decide) (by decide) h0
  have t1 := copy_eval a1 (secondSource swapped) 1
    (by cases swapped <;> decide) (by cases swapped <;> decide) (by decide)
    (by cases swapped <;> simp [a1, copyStacks, h0, firstSource])
  have t2 := copy_eval a2 16 12 (by decide) (by decide) (by decide)
    (by cases swapped <;> simp [a2, a1, copyStacks, h0, firstSource, secondSource])
  have t3 := copy_eval a3 15 12 (by decide) (by decide) (by decide)
    (by cases swapped <;> simp [a3, a2, a1, copyStacks, h0, firstSource, secondSource])
  have he : copied a3 15 12 = prepared a swapped := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; cases swapped <;> fin_cases j <;>
        simp [a3, a2, a1, readRegs]
    · funext j; cases swapped <;> fin_cases j <;>
        simp [a3, a2, a1, copyStacks, leftWord,
          firstSource, secondSource, h1, h12]
  have ht := t0.seq (t1.seq (t2.seq t3))
  rw [he] at ht
  convert ht using 1
  cases swapped <;> simp [a3, a2, a1, copyStacks, firstSource, secondSource, volume] <;> ring

abbrev comparePair (swapped : Bool) : Cmd 8 17 := .seq (prepare swapped) equality

def pairMatches (a : Data) (swapped : Bool) : Bool :=
  decide (leftWord a swapped = a.stacks 15 ++ a.stacks 16)

theorem comparePair_eval (a : Data) (swapped : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 18 * volume a + 40,
      Eval (comparePair swapped) n a (compared a (pairMatches a swapped)) := by
  have hp := prepare_eval a swapped h0 h1 h12
  obtain ⟨n, hn, he⟩ := equality_eval (prepared a swapped)
  have hfinish : compared (prepared a swapped)
      (decide ((prepared a swapped).stacks 1 = (prepared a swapped).stacks 12)) =
      compared a (pairMatches a swapped) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [ readRegs]
    · funext j; fin_cases j <;> simp [ pairMatches]
  rw [hfinish] at he
  refine ⟨7 * volume a + 20 + n, ?_, hp.seq he⟩
  cases swapped <;> simp [ leftWord, List.length_append, volume] at hn ⊢ <;> omega

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
