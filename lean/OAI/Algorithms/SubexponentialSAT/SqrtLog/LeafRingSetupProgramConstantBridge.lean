import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramBase

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing

/-- Reconstruct only the unconstrained fields of the constant generator's
local store.  Its service-owned scratch is checked separately below. -/
def constantStore (out : Fin 640) (a : Data) : RingProgramTable.Store where
  modulus := a.stacks (constant out 5)
  left := a.stacks 538
  source := a.stacks (constant out 9)
  saved := a.stacks (constant out 10)
  width := a.stacks (constant out 12)
  coefficients := a.stacks (constant out 16)
  minusOne := a.stacks (constant out 17)
  tail := a.stacks (constant out 18)
  polynomial := a.stacks (constant out 21)
  degree := a.stacks 204
  zero := a.stacks 203
  powers := a.stacks (constant out 25)
  rounds := a.stacks (constant out 26)

def constantScratch : List (Fin 27) :=
  [1,2,3,4,6,7,8,11,13,14,15,19,20,23]

/-- This form of the constant service exposes its complete physical write
set: the consumed seed and one output.  All other local and global tapes
are retained, so the three calls can safely reuse the same workspace. -/
theorem constantCall_produces (a : Data) (out : Fin 640)
    (hi : Function.Injective (constant out)) {B : ℕ}
    (seed zeroWord : Word B)
    (hseed : a.stacks 538=seed.val) (hzero : a.stacks 203=zeroWord.val)
    (hc : ∀ i∈constantScratch, a.stacks (constant out i)=[]) :
    ∃ n ≤ LeafProgram.Constants.budget B (a.stacks 204).length+1,
      ∃ e : Data, Eval (constantCall out) n a e ∧
      e.stacks=Function.update (Function.update a.stacks 538 []) out
        (RingProgramTable.literalBits (a.stacks 204).length seed zeroWord) := by
  let s := constantStore out a
  let r := (projectState (registers 8 (by decide)) (constant out) a).regs
  have hin : projectState (registers 8 (by decide)) (constant out) a =
      RingProgramTable.state r (LeafProgram.Constants.input s seed zeroWord) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [ RingProgramTable.tapes,
          LeafProgram.Constants.input, s, constantStore, constant,
          hseed, hzero]
      all_goals first
        | exact hc 1 (by decide)
        | exact hc 2 (by decide)
        | exact hc 3 (by decide)
        | exact hc 4 (by decide)
        | exact hc 6 (by decide)
        | exact hc 7 (by decide)
        | exact hc 8 (by decide)
        | exact hc 11 (by decide)
        | exact hc 13 (by decide)
        | exact hc 14 (by decide)
        | exact hc 15 (by decide)
        | exact hc 19 (by decide)
        | exact hc 20 (by decide)
        | exact hc 23 (by decide)
  obtain ⟨n,hn,rf,he⟩ := constantCall_eval a out hi (a.stacks 204).length
    seed zeroWord s r rfl hin
  refine ⟨n,hn,_,he,?_⟩
  have hlocal :
      (RingProgramTable.state rf
        (LeafProgram.Constants.output s (a.stacks 204).length seed zeroWord)).stacks =
      Function.update (Function.update
        (projectState (registers 8 (by decide)) (constant out) a).stacks 0 []) 15
        (RingProgramTable.literalBits (a.stacks 204).length seed zeroWord) := by
    rw [hin]
    funext i
    fin_cases i <;> simp [RingProgramTable.tapes,
      LeafProgram.Constants.output,LeafProgram.Constants.input]
  change Function.extend (constant out) _ a.stacks = _
  rw [hlocal,ProgramLinking.extend_update hi,ProgramLinking.extend_update hi]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project (registers 8 (by decide)) (constant out) a
      (registers_injective 8 (by decide)) hi)
  change Function.extend (constant out)
    (projectState (registers 8 (by decide)) (constant out) a).stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
