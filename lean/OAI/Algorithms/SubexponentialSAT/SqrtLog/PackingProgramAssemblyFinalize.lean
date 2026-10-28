import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyWeights

namespace OAI.Algorithms

/-! End-to-end native weighting, serialization, and scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev clearWeight (i : Fin 48) : Cmd 16 48 := .call (SubexponentialSAT.StackRoutines.clearProgram i 0 1)
abbrev weightAndMerge : Cmd 16 48 := .seq weights (.seq (.seq merge finishMerged)
  (.seq (clearWeight 15) (clearWeight 16)))

theorem weightAndMerge_eval (d : Data) (ps : List (ℕ × ℕ)) (h : inputPairScores d ps) :
    ∃ wi wh : List Bool,
      SubexponentialSAT.BinaryArithmetic.toNat wi=(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20))^2*
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 21))^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat wh=8*(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 22))^2*
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 23))^2 ∧
      wi.length ≤ 2*(d.stacks 20).length+2*(d.stacks 21).length+3 ∧
      wh.length ≤ 2*(d.stacks 22).length+2*(d.stacks 23).length+6 ∧
      ∃ t ≤ 500*(2*dataLength d+4)^2+1+Zip.budget wi wh ps+
        6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+
        2*wi.length+2*wh.length+14,
        ∃ e : Data, Eval weightAndMerge t d e ∧
          e.stacks 0=ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
          e.stacks 12=[] ∧
          (∀ j,j≠0→j≠12→e.stacks j=d.stacks j) := by
  have hw : WeightReady d := by
    intro i hi
    fin_cases i <;> try (norm_num at hi)
    all_goals simpa [weightPorts] using h.2.2 _ (by simp)
  obtain ⟨tw,htw,b,hb,hi,hh,hli,hlh,hbf⟩ := weights_eval d hw
  obtain ⟨tm,htm,c,hc,ho,h12,hcf⟩ := finishMerged_eval
    (b.stacks 15) (b.stacks 16) ps b (weights_mergeInput d b ps h hbf)
  have hc15 : c.stacks 15=b.stacks 15 := hcf _ (by decide) (by decide)
  have hc16 : c.stacks 16=b.stacks 16 := hcf _ (by decide) (by decide)
  let c₁ : Data := ⟨readRegs c.regs 0 1 none,Function.update c.stacks 15 []⟩
  let c₂ : Data := ⟨readRegs c₁.regs 0 1 none,Function.update c₁.stacks 16 []⟩
  have hcl1 : Eval (clearWeight 15) (2*(c.stacks 15).length+3) c c₁ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 15 0 1 c.regs c.stacks)
  have hcl2 : Eval (clearWeight 16) (2*(c₁.stacks 16).length+3) c₁ c₂ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 16 0 1 c₁.regs c₁.stacks)
  refine ⟨b.stacks 15,b.stacks 16,hi,hh,hli,hlh,
    tw+(tm+((2*(c.stacks 15).length+3)+(2*(c₁.stacks 16).length+3))),?_,
    c₂,hb.seq (hc.seq (hcl1.seq hcl2)),?_,?_,?_⟩
  · have h16 : c₁.stacks 16=b.stacks 16 := by simpa [c₁] using hc16
    rw [hc15,h16]
    omega
  · simpa [c₂,c₁] using ho
  · simpa [c₂,c₁] using h12
  · intro j hj0 hj12
    by_cases hj15 : j=15
    · subst j
      simp [c₂,c₁,h.2.2 15 (by simp)]
    by_cases hj16 : j=16
    · subst j
      simp [c₂,h.2.2 16 (by simp)]
    · simp only [c₂,c₁,Function.update_of_ne hj15,Function.update_of_ne hj16]
      exact (hcf j hj0 hj12).trans (hbf j hj15 hj16)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
