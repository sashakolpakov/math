import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchProgram

namespace OAI.Algorithms

/-! The physical search invariant is shared by candidate generation and
first-success scanning, without either execution proof depending on the other. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchProgram

open MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

/-- Mutable answer/candidate registers are unrestricted; fixed field and
interval inputs, empty work tapes, and candidate size are retained. -/
def Invariant (A R : ℕ) (alphabet : List Bool) (d : Data) : Prop :=
  ∃ (regs : Fin 8 → Bool) (g neg ok tag present found : Bool)
    (selected source payload : List Bool),
    d = wide (blank p R regs g neg ok) tag present found selected source payload
      alphabet (List.replicate A true) ∧ selected.length ≤ R * (2 * width p + 1)

end SubexponentialSAT.Subexp.CoefficientSearchProgram

end OAI.Algorithms
