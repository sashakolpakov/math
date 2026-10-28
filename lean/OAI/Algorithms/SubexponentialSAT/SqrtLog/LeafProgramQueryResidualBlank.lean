import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryProperty
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramResidualFrame

namespace OAI.Algorithms

/-! The seven residual scratch tapes are preserved by the actual full query
setup. In particular the initial blank workspace remains blank. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem Preparation.residual_frame {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (h728 : a.stacks 728=[]) (i : Fin 768)
    (hi : LeafRingSetupProgram.ResidualFrame.residualTape i) : p.out.stacks i=a.stacks i := by
  have hbank := ring_bank_of_frame p.front p.packed p.bankWords _ p.frontOutput.bank
    (fun i hi hj => p.packingFrame i (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
  have hf728 : p.front.stacks 728=a.stacks 728 := p.frontOutput.frame _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp728 : p.packed.stacks 728=[] :=
    (p.packingFrame _ (by decide) (by decide) (by decide)).trans (hf728.trans h728)
  let ms := Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)
  have hframe := arithmetic_property p.packed p.out p.arithmeticSteps p.arithmeticExecution
    _ p.bankWords _ p.frontOutput.shape hbank
    (Finset.univ.sup (fun i => (p.packed.stacks i).length))
    (Finset.univ.sup ms.val) (Finset.univ.sup ms.len)
    (fun i => Finset.le_sup (f := fun j : Fin 768 => (p.packed.stacks j).length) (Finset.mem_univ i))
    (fun i => Finset.le_sup (Finset.mem_univ i))
    (fun i => Finset.le_sup (Finset.mem_univ i))
    (ring_precision_pos (q.input k) p.lengths hg) (ring_degree_pos (q.input k) p.lengths hg)
    (ring_exponent (q.input k) p.lengths hg) hp728 i
    (by
      simp only [LeafRingSetupProgram.ResidualFrame.residualTape,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    (p.packed.stacks i) (fun nr b he => LeafRingSetupProgram.ResidualFrame.producerWideCall_frame he i hi)
  apply hframe.trans
  have hfront : p.front.stacks i=a.stacks i := by
    simp only [LeafRingSetupProgram.ResidualFrame.residualTape,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact (p.frontOutput.frame _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide))
  apply Eq.trans _ hfront
  simp only [LeafRingSetupProgram.ResidualFrame.residualTape,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact p.packingFrame _ (by decide) (by decide) (by decide)

theorem Preparation.residual_empty {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (h728 : a.stacks 728=[]) (i : Fin 768)
    (hi : LeafRingSetupProgram.ResidualFrame.residualTape i) (hz : a.stacks i=[]) :
    p.out.stacks i=[] := (p.residual_frame h728 i hi).trans hz

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
