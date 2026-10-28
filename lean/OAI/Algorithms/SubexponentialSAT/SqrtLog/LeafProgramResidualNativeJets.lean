import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeSamples
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModel

namespace OAI.Algorithms

/-! Typed CRT arrays are formed from the actual dense readout witnesses.
There is no canonical-byte selection or re-encoding assumption. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

section
variable {n d : ℕ} (p t : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
  (entries : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
  (u : ℕ) (zero : RingProgram.Code (Word (baseWidth p t)) d)

 theorem readout_codes_length (z J : ℕ) :
    (MomentsReadoutProgram.outputCodes p t M cache entries u zero z J).length=J := by
  induction J generalizing z with
  | zero => rfl
  | succ J ih =>
    simp only [MomentsReadoutProgram.outputCodes,List.length_cons,ih]

 def readoutJet (J : ℕ) : CRTLocalProgram.Model.Poly (baseWidth p t) d J :=
  ⟨MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J,
    readout_codes_length p t M cache entries u zero 0 J⟩

 theorem readoutJet_encode (J : ℕ) :
    Fixed.encode (readoutJet p t M cache entries u zero J)=
      MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J := rfl
end

 theorem sampled_readout_jets {n d Q : ℕ} (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (entries : Fin Q → List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (u J : ℕ) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (a : Data) (nodes : ℕ → List Bool) (regs : Fin 40 → Bool) :
    (sampled a nodes (fun i => MomentsReadoutProgram.outputBits p t M cache (entries i) u zero 0 J) regs).stacks 265=
      (List.finRange Q).flatMap (fun i => Fixed.encode (readoutJet p t M cache (entries i) u zero J)) := by
  rw [sampled_jets]
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
