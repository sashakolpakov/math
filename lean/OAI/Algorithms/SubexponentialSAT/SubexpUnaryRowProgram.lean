import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram
import OAI.Algorithms.SubexponentialSAT.RankAssignmentLift
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationSchedule
import OAI.Algorithms.SubexponentialSAT.CounterWidth
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!+# Actual unary-validity table rows

Each scalar rank is padded to the modulus word's width, then tested by the
checked unary-validity program with the actual chunk-width word. The callback
preserves the rank, fuel, modulus, and chunk width, and emits one Boolean bit.
-/

namespace SubexponentialSAT.SubexpUnaryRowProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 16

def Clean (stk : Fin 16 → List Bool) : Prop := ∀ i : Fin 10, stk (i.castAdd 6) = []

def answer (width rank : ℕ) : Bool := decide (rank < 2 ^ width)

def rowRegister (i : Fin 3) : Fin 8 := i.castAdd 5
def rowStack (i : Fin 4) : Fin 16 := i.castAdd 12

theorem rowRegister_injective : Function.Injective rowRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem rowStack_injective : Function.Injective rowStack := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

abbrev zeroThree (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 false) 2 false

abbrev resetThree : Cmd 8 16 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

theorem resetThree_eval (regs : Fin 8 → Bool) (stk : Fin 16 → List Bool) :
    Eval resetThree 3 ⟨regs, stk⟩ ⟨zeroThree regs, stk⟩ := by
  have h0 : Eval (.base (.atom (.set 0 false))) 1 (⟨regs, stk⟩ : Data)
      ⟨Function.update regs 0 false, stk⟩ := .base (.atom _ _)
  have h1 : Eval (.base (.atom (.set 1 false))) 1
      (⟨Function.update regs 0 false, stk⟩ : Data)
      ⟨Function.update (Function.update regs 0 false) 1 false, stk⟩ := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 2 false))) 1
      (⟨Function.update (Function.update regs 0 false) 1 false, stk⟩ : Data)
      ⟨zeroThree regs, stk⟩ := .base (.atom _ _)
  exact h0.seq (h1.seq h2)

abbrev rowInput (stk : Fin 16 → List Bool) (label width : List Bool) : Fin 16 → List Bool :=
  Function.update (Function.update stk 0 label) 2 width

abbrev rowOutput (stk : Fin 16 → List Bool) (result : Bool) : Fin 16 → List Bool :=
  Function.update stk 1 [result]

abbrev validityCall : Cmd 8 16 :=
  .seq resetThree (.call (ProgramLinking.liftProgram
    SubexpFactorProgram.UnaryValidity.program rowRegister rowStack))

theorem validity_eval (low high width : List Bool) (hw : width.length = low.length)
    (regs : Fin 8 → Bool) (stk : Fin 16 → List Bool) (hc : Clean stk) :
    Eval validityCall (6 * low.length + 4 * high.length + 17)
      ⟨regs, rowInput stk (low ++ high) width⟩
      ⟨zeroThree regs, rowOutput stk (SubexpFactorProgram.allZero high)⟩ := by
  have h0 : stk 0 = [] := hc 0
  have h1 : stk 1 = [] := hc 1
  have h2 : stk 2 = [] := hc 2
  have h3 : stk 3 = [] := hc 3
  let d : Data := ⟨zeroThree regs, rowInput stk (low ++ high) width⟩
  have hin : embedState rowRegister rowStack d
      (SubexpFactorProgram.UnaryValidity.inputState (low ++ high) width) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ rowRegister_injective rowStack_injective
    · intro i
      fin_cases i <;> simp [d, rowRegister, zeroThree
        ]
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [d, rowStack, rowInput, h1, h3]
    · intro i hi; rfl
  have hout : embedState rowRegister rowStack d
      (StructuredProgram.ioState (1 : Fin 4) [SubexpFactorProgram.allZero high]) =
      (⟨zeroThree regs, rowOutput stk (SubexpFactorProgram.allZero high)⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ rowRegister_injective rowStack_injective
    · intro i
      fin_cases i <;> simp [rowRegister, zeroThree ]
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [rowStack, rowOutput, h0, h2, h3]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
      simp [d, rowInput, rowOutput, h0, h1, h2]
  have ht := eval_call_lifted SubexpFactorProgram.UnaryValidity.program rowRegister rowStack d
    rowRegister_injective rowStack_injective
    (SubexpFactorProgram.UnaryValidity.trace low high width hw)
  rw [hin, hout] at ht
  have he := (resetThree_eval regs (rowInput stk (low ++ high) width)).seq ht
  convert he using 1
  omega

def paddingPorts : Fin 6 ↪ Fin 16 := ⟨![10, 13, 0, 4, 5, 6], by decide⟩

abbrev body : Cmd 8 16 :=
  .seq (.call (RankAssignmentLift.programAt paddingPorts))
    (.seq (.call (copyProgram 14 2 7 0 1))
      (.seq validityCall (.call (transferProgram 1 15 0 1))))

theorem body_eval (rank modulus width : List Bool) (regs : Fin 8 → Bool)
    (stk : Fin 16 → List Bool) (hc : Clean stk)
    (hrank : stk 10 = rank) (hmodulus : stk 13 = modulus) (hwidth : stk 14 = width)
    (hrankLen : rank.length ≤ modulus.length) (hwidthLen : width.length ≤ modulus.length) :
    ∃ rf : Fin 8 → Bool,
      Eval body (7 * rank.length + 14 * modulus.length + 13 * width.length +
        4 * (modulus.length - width.length) + 45)
        ⟨regs, stk⟩
        ⟨rf, Function.update stk 15 (answer width.length (CounterPrograms.value rank) :: stk 15)⟩ := by
  have h1 : stk 1 = [] := hc 1
  have h2 : stk 2 = [] := hc 2
  let word := ModularArithmetic.padTo modulus rank
  let low := word.take width.length
  let high := word.drop width.length
  have hwordLen : word.length = modulus.length := ModularArithmetic.padTo_length _ _
  have hlow : low.length = width.length := by
    simp only [low, List.length_take, hwordLen, Nat.min_eq_left hwidthLen]
  have hhigh : high.length = modulus.length - width.length := by simp [high, hwordLen]
  have happend : low ++ high = word := List.take_append_drop _ _
  have hans : SubexpFactorProgram.allZero high = answer width.length (CounterPrograms.value rank) := by
    rw [SubexpFactorProgram.UnaryValidity.result_correct low high, hlow, happend]
    have hv : BinaryArithmetic.toNat word = CounterPrograms.value rank := by
      rw [CounterPrograms.value_eq_toNat]
      exact ModularArithmetic.padTo_correct modulus rank hrankLen
    rw [hv]
    rfl
  obtain ⟨r₁, hp, _⟩ := RankAssignmentLift.programAt_eval paddingPorts rank modulus regs stk
    hrank hmodulus hrankLen (hc 0) (hc 4) (hc 5) (hc 6)
  change Eval (.call (RankAssignmentLift.programAt paddingPorts)) _ ⟨regs, stk⟩
    ⟨r₁, Function.update stk 0 word⟩ at hp
  have hcopy : Eval (.call (copyProgram (14 : Fin 16) 2 7 (0 : Fin 8) 1))
      (7 * width.length + 5) ⟨r₁, Function.update stk 0 word⟩
      ⟨readRegs r₁ 0 1 none, rowInput stk word width⟩ := by
    have ht := ListRegisterProgram.copy_run (14 : Fin 16) 2 7 (0 : Fin 8) 1
      (by decide) (by decide) (by decide) (by decide) r₁
      (Function.update stk 0 word) (by simpa using hc 7)
    apply Eval.call
    have heq : copyStacks 14 2 (Function.update stk 0 word) = rowInput stk word width := by
      funext i
      simp [copyStacks, rowInput, hwidth, h2]
    rw [heq] at ht
    simpa [hwidth] using ht
  have hv := validity_eval low high width hlow.symm (readRegs r₁ 0 1 none) stk hc
  rw [happend, hans] at hv
  have htransfer : Eval (.call (transferProgram (1 : Fin 16) 15 (0 : Fin 8) 1)) 6
      ⟨zeroThree (readRegs r₁ 0 1 none), rowOutput stk (answer width.length (CounterPrograms.value rank))⟩
      ⟨readRegs (zeroThree (readRegs r₁ 0 1 none)) 0 1 none,
        Function.update stk 15 (answer width.length (CounterPrograms.value rank) :: stk 15)⟩ := by
    apply Eval.call
    have ht := ListRegisterProgram.transfer_run (1 : Fin 16) 15 (0 : Fin 8) 1
      (by decide) (by decide) (zeroThree (readRegs r₁ 0 1 none))
      (rowOutput stk (answer width.length (CounterPrograms.value rank)))
    have heq : transferStacks 1 15 (rowOutput stk (answer width.length (CounterPrograms.value rank))) =
        Function.update stk 15 (answer width.length (CounterPrograms.value rank) :: stk 15) := by
      funext i
      fin_cases i <;> simp [transferStacks, rowOutput, h1]
    rw [heq] at ht
    simpa [rowOutput] using ht
  refine ⟨readRegs (zeroThree (readRegs r₁ 0 1 none)) 0 1 none, ?_⟩
  have he := hp.seq (hcopy.seq (hv.seq htransfer))
  convert he using 1 ; simp only [hlow, hhigh] ; omega

end SubexponentialSAT.SubexpUnaryRowProgram

end OAI.Algorithms
