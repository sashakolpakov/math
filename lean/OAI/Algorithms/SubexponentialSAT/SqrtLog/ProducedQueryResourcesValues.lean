import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesPacking
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesDomination
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyParameterValues

namespace OAI.Algorithms

/-! Choose one fixed ordinary exponent containing every actual serialized
numeric parameter. Arbitrary input-word padding is absent from numeric
values; its cost remains an explicit input-length polynomial. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open LeafQueryFrontend LeafParametersProgram
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem exists_value_cap : ∃ e : ℕ, 13 ≤ e ∧
    ∀ (q : Query) (k B C d qi n : ℕ), 2 ≤ n → ambient q=n → SmallInputs q k n →
    ∀ (hg : Guard (q.input k))
      (a : Word (problem q k hg).r (problem q k hg).Q)
      (tail : List (Word (problem q k hg).r (problem q k hg).Q))
      (l : Fin 8 → ℕ) (j : Fin 64),
      (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val j ≤
        (ofPacking q k B C d qi e hg a tail).bits := by
  obtain ⟨Cval,dval,hval⟩ := CostAssembly.ParameterValues.serialized_values_of_fourth_power
  refine ⟨Cval+dval+13,by omega,?_⟩
  intro q k B C d qi n hn hqn hs hg a tail l j
  have hh := (hval (q.input k) l n hs.magnitude j).trans
    (coefficient_power_le Cval dval n (Cval+dval+13) hn (by omega))
  simpa only [ofPacking,make,hqn] using hh

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
