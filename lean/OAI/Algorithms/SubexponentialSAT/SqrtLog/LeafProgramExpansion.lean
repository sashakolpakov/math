import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopFinal

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768

def register (i : Fin 8) : Fin 40 := i.castAdd 32

def stackMap : Fin 24 → Fin 768 :=
  ![154,708,340,341,342,343,344,707,345,346,347,348,
    349,350,700,280,64,351,352,353,354,355,356,357]

theorem register_injective : Function.Injective register :=
  Fin.castAdd_injective 8 32

theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev command : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram HashInputProgram.Loop.assembleProgram register stackMap)

def scratch : List (Fin 768) :=
  [340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357]

def outputWord (t d : ℕ) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) : List Bool :=
  Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses))

noncomputable def finished (a : Data) (rf : Fin 8 → Bool) (word : List Bool) : Data :=
  embedState register stackMap a
    (HashInputProgram.Loop.data rf [] (a.stacks 708) (a.stacks 707)
      (a.stacks 700) (a.stacks 280) word [] [] [] [])

/-- The only inputs besides the actual row/source bytes are represented
runtime dimensions.  In particular, the theorem does not assume a supplied
inline row or a trace for a source lookup. -/
theorem command_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (a : Data)
    (hraw : a.stacks 154=HashInputProgram.Loop.rawInput b terms)
    (hsource : a.stacks 700=Encoding.encodeList id clauses)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=clauses.length)
    (hshape : (a.stacks 280).length=(d+1)*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hwork : ∀ i∈scratch, a.stacks i=[]) :
    ∃ k rf, k ≤ HashInputProgram.Loop.uniformBudget t d b (a.stacks 707)
        clauses terms.length+3 ∧
      Eval command k a (finished a rf (outputWord t d clauses terms)) := by
  obtain ⟨rf,k,hk,he⟩ := HashInputProgram.Loop.assemble_runs t d ht b hb clauses terms
    hbound (a.regs ∘ register) (a.stacks 708) (a.stacks 707) (a.stacks 280)
    hwidth hmodulus hshape
  have hi : projectState register stackMap a =
      HashInputProgram.Loop.data (a.regs ∘ register)
        (HashInputProgram.Loop.rawInput b terms) (a.stacks 708) (a.stacks 707)
        (Encoding.encodeList id clauses) (a.stacks 280) [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        first | exact hraw | exact hsource | exact houtput | rfl | exact hwork _ (by decide)
  rw [← hi] at he
  have lifted := eval_call_from_state HashInputProgram.Loop.assembleProgram
    register stackMap a register_injective stackMap_injective he
  refine ⟨k,rf,hk,?_⟩
  simpa only [command,finished,outputWord,hsource] using lifted

theorem finished_output (a : Data) (rf : Fin 8 → Bool) (word : List Bool) :
    (finished a rf word).stacks 64=word := by
  change (finished a rf word).stacks (stackMap 16)=word
  exact embedState_stack register stackMap a _ stackMap_injective 16

theorem finished_input (a : Data) (rf : Fin 8 → Bool) (word : List Bool) :
    (finished a rf word).stacks 154=[] := by
  change (finished a rf word).stacks (stackMap 0)=[]
  exact embedState_stack register stackMap a _ stackMap_injective 0

theorem finished_frame (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : ¬∃ j, stackMap j=i) :
    (finished a rf word).stacks i=a.stacks i :=
  embedState_stack_frame register stackMap a _ i hi

theorem finished_register_frame (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (finished a rf word).regs i=a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
