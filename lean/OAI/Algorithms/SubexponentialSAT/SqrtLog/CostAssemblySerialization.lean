import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

/-! Exact ordinary cost of the two derived numeric metadata words. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafParametersProgram


def serializationEnvelope (S : ℕ) : ℕ :=
  (2*S+3)+(7*S+5)+20*(S+1)+20*(S+1)+(2*S+3)+100*(S+S+1)^2

theorem serialization_budget_le (m : Circuit.Model) (S : ℕ)
    (hl : ∀ i, m.len i ≤ S) :
    Circuit.budget Serialization.code m ≤ serializationEnvelope S := by
  have he : Circuit.budget Serialization.code m =
      (2*m.len 44+3)+(7*m.len 35+5)+20*(m.len 35+1)+20*(m.len 35+1)+
      (2*m.len 45+3)+100*(m.len 33+m.len 33+1)^2 := by
    have h35 : (35 : Fin 64)≠44 := by decide
    have h45 : (45 : Fin 64)≠44 := by decide
    have h33a : (33 : Fin 64)≠45 := by decide
    have h33b : (33 : Fin 64)≠44 := by decide
    norm_num [Serialization.code,Circuit.budget,Circuit.cost,Circuit.next,
      Circuit.output,Circuit.lengthBound,Function.update,h35,h45,h33a,h33b]
    ; ring
  rw [he]
  unfold serializationEnvelope
  gcongr <;> exact hl _

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
