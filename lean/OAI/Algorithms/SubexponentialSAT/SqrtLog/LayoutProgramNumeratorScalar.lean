import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNumerator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarFromCounts

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
variable {r Q : ℕ}

theorem scalar_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R d : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) (h : List Bool)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ LayoutProgramScalar.FromCounts.totalCost a.length R d h.length width.length (pairLength power),
      ∃ rf result, Eval scalar n (state c regs t u y (List.replicate (d+1) true) h ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨rr,result,⟨n,hn,he⟩,hv,hm,hl⟩ := LayoutProgramScalar.FromCounts.program_runsIn
    Hwords width power (regs ∘ scalarRegs) a h R d Q hlen hwords hvalues hp hpt hwidth hAQ hQ hhQ
  let start := state c regs t u y (List.replicate (d+1) true) h ([],[])
  have hh := eval_call_from_state LayoutProgramScalar.FromCounts.program scalarRegs scalarPorts start
    scalarRegs_inj scalarPorts_inj (by rw [scalar_project]; exact he)
  rw [scalar_embed] at hh
  exact ⟨n,hn,_,result,hh,hv,hm,hl⟩


end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
