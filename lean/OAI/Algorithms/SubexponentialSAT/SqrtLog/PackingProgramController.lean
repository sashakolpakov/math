import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramCounts
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialStep
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! The fixed dynamic assignment controller, specialized to the new exact
weighted scores. The producer contract is explicit and must be discharged by
an actual score-stream program; it is not a unit-cost score operation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def selectedValues (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights) :
    List (Word r Q) :=
  NaturalAssignment.assignNat a tail
    (sequentialNumerator ivar factor (a::tail) terms indices w a) indices.length []

omit [Fintype E] [DecidableEq I] in
theorem selectedValues_eq_computedWords (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator) :
    (fun i => decode a (selectedValues ivar factor a tail terms indices w) (indexCode indices i)) =
      computedWords ivar factor a tail terms indices x y := by
  unfold selectedValues computedWords localAssign
  rw [naturalAssignment_eq ivar factor a tail terms indices w x y hy hx]

/-- The only remaining producer obligation is execution of a fixed command
which writes actual framed unary scores and restores the controller frame. -/
abbrev ScoreProducer (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (builder : Cmd 16 48) (cost : ℕ) (environment : Fin 48 → List Bool) : Prop :=
  SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
    (sequentialNumerator ivar factor (a::tail) terms indices w a)
    builder cost indices.length environment

def scoreBound (terms : List (ScoreTerm I V Q)) (w : Weights) (q : ℕ) : ℕ :=
  terms.length * ((w.incidence+w.head)*q^4)

def controllerBudget (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E))
    (w : Weights) (q width cost : ℕ) : ℕ :=
  indices.length * (cost + SequentialProgram.selectionBudget q
    (scoreBound terms w q) indices.length width + 3) + 3

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- All candidate and coordinate loops are existing fixed bit-machine loops.
Their cost is included. This theorem remains conditional on the concrete
producer's execution theorem, which is displayed in its type. -/
theorem controller_runsIn (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (builder : Cmd 16 48) (cost : ℕ) (environment : Fin 48 → List Bool)
    (hproducer : ScoreProducer ivar factor a tail terms indices w builder cost environment)
    (d : SequentialProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail indices.length [] d.stacks)
    (hc : (d.stacks 11).length = indices.length)
    (he : SequentialProgram.HighState environment d.stacks) :
    ∃ e : SequentialProgram.Data,
      RunsIn (SequentialProgram.program builder)
        (controllerBudget terms indices w (a::tail).length (ReadPlan.encodeWord a).length cost)
        (d.withPC (some (SequentialProgram.program builder).entry)) (e.withPC none) ∧
      e.stacks 8 = ((selectedValues ivar factor a tail terms indices w).reverse.map
        ReadPlan.encodeWord).flatten := by
  apply SequentialProgram.program_of_scoreBuilder ReadPlan.encodeWord a tail
    (sequentialNumerator ivar factor (a::tail) terms indices w a) builder cost
    (scoreBound terms w (a::tail).length) indices.length environment
  · intro z
    simp [ReadPlan.encodeWord_length]
  · intro n fixed z hsize hz
    exact numerator_bound ivar factor (a::tail) terms indices w
      (List.range' (z::fixed).length n) List.nodup_range' (decode a (z::fixed))
  · exact hproducer
  · exact hm
  · exact hc
  · exact he

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem controller_primitive (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (builder : Cmd 16 48) (cost : ℕ) (environment : Fin 48 → List Bool)
    (hproducer : ScoreProducer ivar factor a tail terms indices w builder cost environment)
    (d : SequentialProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail indices.length [] d.stacks)
    (hc : (d.stacks 11).length = indices.length)
    (he : SequentialProgram.HighState environment d.stacks) :
    ∃ e : SequentialProgram.Data,
      SubexponentialSAT.Computation.RunsIn (primitive (SequentialProgram.program builder)).step
        (primitiveOverhead (SequentialProgram.program builder) *
          controllerBudget terms indices w (a::tail).length (ReadPlan.encodeWord a).length cost)
        (primitiveCfg (SequentialProgram.program builder)
          (d.withPC (some (SequentialProgram.program builder).entry)))
        (primitiveCfg (SequentialProgram.program builder) (e.withPC none)) ∧
      e.stacks 8 = ((selectedValues ivar factor a tail terms indices w).reverse.map
        ReadPlan.encodeWord).flatten := by
  obtain ⟨e, hr, hout⟩ := controller_runsIn ivar factor a tail terms indices w
    builder cost environment hproducer d hm hc he
  exact ⟨e, primitive_execution (SequentialProgram.program builder) hr, hout⟩
end Controller
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
