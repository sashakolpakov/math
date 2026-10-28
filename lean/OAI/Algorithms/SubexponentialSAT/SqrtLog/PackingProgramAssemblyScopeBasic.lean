import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyNative

namespace OAI.Algorithms

/-! Retain the final memory invariant of the checked sequential loop. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem program_memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (builder : Cmd 16 48) (cost bound total : ℕ)
    (env : Fin 48 → List Bool)
    (hwidth : ∀ x, (encode x).length=(encode a).length)
    (hscore : ∀ n fixed x, n+1+fixed.length ≤ total → x∈a::tail → evaluate n (x::fixed) ≤ bound)
    (hbuilder : SequentialProgram.ScoreBuilderRefines encode a tail evaluate builder cost total env)
    (d : Data) (hm : SequentialProgram.Memory encode a tail total [] d.stacks)
    (hc : (d.stacks 11).length=total) (he : SequentialProgram.HighState env d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program builder)
      (total*(cost+SequentialProgram.selectionBudget (a::tail).length bound total (encode a).length+3)+3)
      (d.withPC (some (SequentialProgram.program builder).entry)) (e.withPC none) ∧
      SequentialProgram.Memory encode a tail 0
        (NaturalAssignment.assignNat a tail evaluate total []) e.stacks ∧
      e.stacks 11=[] ∧ SequentialProgram.HighState env e.stacks := by
  have hstep := SequentialProgram.stepRefines_of_scoreBuilder encode a tail evaluate builder
    cost bound total env hwidth hscore hbuilder
  obtain ⟨t,ht,e,hr,hem,hc',he'⟩ := SequentialProgram.loop_eval encode a tail evaluate builder
    (cost+SequentialProgram.selectionBudget (a::tail).length bound total (encode a).length)
    total env hstep total [] d (by simp) hm hc he
  exact ⟨e,⟨(1+t)+1,by omega,
    compiled_halt_trace ((SequentialProgram.peek_eval d).seq hr) 8 8⟩,hem,hc',he'⟩

theorem assign_length {A : Type*} (a : A) (tail : List A)
    (evaluate : ℕ → List A → ℕ) (n : ℕ) (fixed : List A) :
    (NaturalAssignment.assignNat a tail evaluate n fixed).length=n+fixed.length := by
  induction n generalizing fixed with
  | zero => simp [NaturalAssignment.assignNat]
  | succ n ih => simp only [NaturalAssignment.assignNat,ih,List.length_cons]; omega

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
