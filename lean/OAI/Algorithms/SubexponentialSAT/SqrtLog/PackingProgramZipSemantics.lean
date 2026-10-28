import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramZip
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramReducedWeights

namespace OAI.Algorithms

/-! Exact output semantics of the native weighted-stream merger. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem scores_map {A : Type*} (xs : List A) (f g : A → ℕ) (wi wh : List Bool) :
    Streams.scores wi wh (xs.map (fun x => (f x,g x))) =
      xs.map (fun x => SubexponentialSAT.Subexp.UnaryCompare.encode
        (SubexponentialSAT.CounterPrograms.value wi*f x+SubexponentialSAT.CounterPrograms.value wh*g x)) := by
  simp [Streams.scores,Streams.value,SubexponentialSAT.Subexp.UnaryCompare.encode,List.map_map,Function.comp_def]

 theorem scores_reduced {A : Type*} (xs : List A) (f g : A → ℕ)
    (wi wh : List Bool) (n s M r : ℕ)
    (hi : SubexponentialSAT.BinaryArithmetic.toNat wi = n^2*s^2)
    (hh : SubexponentialSAT.BinaryArithmetic.toNat wh = 8*M^2*r^2) :
    Streams.scores wi wh (xs.map (fun x => (f x,g x))) =
      xs.map (fun x => SubexponentialSAT.Subexp.UnaryCompare.encode (reducedScore n s M r (f x) (g x))) := by
  rw [scores_map]
  apply List.map_congr_left
  intro x hx
  rw [SubexponentialSAT.CounterPrograms.value_eq_toNat, SubexponentialSAT.CounterPrograms.value_eq_toNat, hi, hh,
    reducedScore_weights]

 theorem program_reducedScores {A : Type*} (xs : List A) (f g : A → ℕ)
    (regs : Fin 8 → Bool) (wi wh : List Bool) (n s M r : ℕ)
    (hi : SubexponentialSAT.BinaryArithmetic.toNat wi = n^2*s^2)
    (hh : SubexponentialSAT.BinaryArithmetic.toNat wh = 8*M^2*r^2) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(budget wi wh (xs.map (fun x => (f x,g x)))+1))
      (primitiveCfg program ((input regs wi wh (xs.map (fun x => (f x,g x)))).withPC
        (some program.entry))) (primitiveCfg program (e.withPC none)) ∧
      e.stacks 8 = SubexponentialSAT.ProgramEncoding.encodeRecords
        (xs.map (fun x => SubexponentialSAT.Subexp.UnaryCompare.encode (reducedScore n s M r (f x) (g x)))) ∧
      e.stacks 12 = wi ∧ e.stacks 13 = wh ∧
      (∀ j, j ≠ 8 → j ≠ 12 → j ≠ 13 → e.stacks j = []) := by
  simpa only [scores_reduced xs f g wi wh n s M r hi hh] using
    program_primitive regs wi wh (xs.map (fun x => (f x,g x)))
end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
