import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmeticState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem constructArithmetic (base : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (h728 : base.stacks 728=[]) : Nonempty (ArithmeticPreparation base m ht hd W V L) := by
  obtain ⟨n,hn,e,M,cache,u,out,he,ho,hi⟩ :=
    arithmetic_eval base m w r hs ha W V L hinit hv hw ht hd hexp h728
  exact ⟨{
    out := out, ringState := e, modulus := M, scalarCache := cache, half := u,
    steps := n, execution := he, time := hn, output := ho, denominatorInverse := hi }⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
