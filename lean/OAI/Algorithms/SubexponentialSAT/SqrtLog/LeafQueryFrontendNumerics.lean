import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCommand

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem finishCall_eval (a : Data) (q u ar : ℕ)
    (hp : projectState r3 finish a = LeafStatisticsProgram.Finalize.state (a.regs ∘ r3) q u ar) :
    ∃ n ≤ 3*u+10, ∃ rf,
      Eval finishCall n a (embedState r3 finish a
        (LeafStatisticsProgram.Finalize.state rf (q+u) 0
          (LeafStatisticsProgram.Finalize.neutralArity ar u))) := by
  obtain ⟨rf,he⟩ := LeafStatisticsProgram.Finalize.program_runsIn (a.regs ∘ r3) q u ar
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r3 finish (registers_injective ..) finish_injective a _ _ he
  exact ⟨n,hn,rf,he⟩

theorem binary_eval (a : Data) (src dst : Fin 768) (input : List Bool)
    (hsd : src≠dst) (hs : src≠647) (hd : dst≠647)
    (hsrc : a.stacks src=input) (hout : a.stacks dst=[]) (htmp : a.stacks 647=[]) :
    ∃ n word b, Eval (binary src dst) n a b ∧
      n ≤ input.length*(8*input.length+10)+5 ∧
      BinaryArithmetic.toNat word=input.length ∧ word.length ≤ input.length ∧
      b.stacks dst=word ∧ b.stacks src=[] ∧ b.stacks 647=[] ∧
      (∀ i, i≠src → i≠dst → i≠647 → b.stacks i=a.stacks i) := by
  have hp : projectState r3 (binaryPorts src dst) a =
      LeafStatisticsProgram.Binary.state (a.regs ∘ r3) input [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [binaryPorts,hsrc,hout,htmp]
  obtain ⟨n,word,b,hn,hv,hl,h0,h1,h2,hr,hframe,he⟩ := LeafStatisticsProgram.Binary.lifted_eval
    r3 (binaryPorts src dst) (registers_injective ..) (binaryPorts_injective src dst hsd hs hd) a input hp
  refine ⟨n,word,b,he,hn,hv,hl,h1,h0,h2,?_⟩
  intro i hi0 hi1 hi2
  apply hframe
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [binaryPorts] at hj <;> simp_all

theorem offsetCall_eval (a : Data) (B Q R : List Bool)
    (hp : projectState r8 offsetPorts a = LayoutOffsetProgram.input (a.regs ∘ r8) B Q R) :
    ∃ n ≤ LayoutOffsetProgram.budget B Q R, ∃ word,
      Eval offsetCall n a (embedState r8 offsetPorts a (LayoutOffsetProgram.result B Q R word)) ∧
      BinaryArithmetic.toNat word=2*BinaryArithmetic.toNat B*(8*BinaryArithmetic.toNat Q)^(2*BinaryArithmetic.toNat R) ∧
      word.length ≤ LayoutOffsetProgram.outputLength B Q R := by
  obtain ⟨word,hv,hl,he⟩ := LayoutOffsetProgram.program_runsIn (a.regs ∘ r8) B Q R
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r8 offsetPorts (registers_injective ..) offsetPorts_injective a _ _ he
  exact ⟨n,hn,word,he,hv,hl⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
