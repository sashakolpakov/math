import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeExport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramScoreWide
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-! Physical fixed-width normalization of the fully accumulated marked mass. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram LeafProgram

def scoreRegisters : Fin 8 → Fin 40 := Fin.castAdd 32
def scoreStacks : Fin 9 → Fin 896 := ![322,323,324,325,326,327,328,329,212]
abbrev normalizeScore : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram Score.program scoreRegisters scoreStacks)

def ScoreReady (a : FrameData) : Prop :=
  ∀ i : Fin 896, 323 ≤ i.val → i.val ≤ 329 → a.stacks i=[]

theorem normalizeScore_eval (a : FrameData) (ha : ScoreReady a) (z : ℕ)
    (hz : z < 2^(a.stacks 212).length) (hv : BinaryArithmetic.toNat (a.stacks 322)=z) :
    ∃ t b, t ≤ 14*(a.stacks 212).length+2*(a.stacks 322).length+15 ∧
      Eval normalizeScore t a b ∧ b.stacks=Function.update a.stacks 322
        (SubexpLiftRing.fixedBits (a.stacks 212).length z) := by
  let d := projectState scoreRegisters scoreStacks a
  have hd : Score.data d.regs (a.stacks 322) [] (a.stacks 212)=d := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [d,projectState,scoreStacks,
        ha 323 (by decide) (by decide),ha 324 (by decide) (by decide),
        ha 325 (by decide) (by decide),ha 326 (by decide) (by decide),
        ha 327 (by decide) (by decide),ha 328 (by decide) (by decide),
        ha 329 (by decide) (by decide)]
  obtain ⟨t,rf,ht,he⟩ := Score.canonical_score_lifted scoreRegisters scoreStacks
    (Fin.castAdd_injective 8 32) (by decide) a d.regs (a.stacks 322) (a.stacks 212) z hz hv
  rw [hd] at he
  dsimp only [d] at he
  rw [embedState_project scoreRegisters scoreStacks a (Fin.castAdd_injective 8 32) (by decide)] at he
  let b := embedState scoreRegisters scoreStacks a
    (Score.data rf (SubexpLiftRing.fixedBits (a.stacks 212).length z) [] (a.stacks 212))
  refine ⟨t,b,ht,he,?_⟩
  funext i
  by_cases hx : ∃ j, scoreStacks j=i
  · obtain ⟨j,rfl⟩ := hx
    rw [show b.stacks (scoreStacks j)=
      (Score.data rf (SubexpLiftRing.fixedBits (a.stacks 212).length z) [] (a.stacks 212)).stacks j from
      embedState_stack _ _ _ _ (by decide) j]
    fin_cases j <;> simp [scoreStacks,
      ha 323 (by decide) (by decide),ha 324 (by decide) (by decide),
      ha 325 (by decide) (by decide),ha 326 (by decide) (by decide),
      ha 327 (by decide) (by decide),ha 328 (by decide) (by decide),
      ha 329 (by decide) (by decide)]
  · have h322 : i≠322 := by intro hi; apply hx; exact ⟨0,hi.symm⟩
    rw [show b.stacks i=a.stacks i from embedState_stack_frame _ _ _ _ i hx]
    simp [h322]

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
