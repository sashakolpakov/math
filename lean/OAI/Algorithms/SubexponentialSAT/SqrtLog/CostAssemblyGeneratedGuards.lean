import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyTrialGuards
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsDecode

namespace OAI.Algorithms

/-! The generated selector alphabet discharges the decoder and family-length
premises of the all-trial guard theorem. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafParametersProgram LeafScopeResourceBounds

theorem eventually_generated_trial_guards (k q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B t d round : ℕ) (clauses : List (List Bool)) (hm : 0 < clauses.length)
        (codes : Fin clauses.length → List ℕ)
        (s : SparseCode.SuppliedShifts clauses.length B)
        (Q : SparseCode.SuppliedLocal clauses.length B)
        (countWord : List Bool) (score : Records → List Bool → List Bool)
        (seed : List Bool) (rest : Records) (bits : List Bool)
        (mark : Option (Fin clauses.length)) (nb tb : List Bool),
      (∀ i, (codes i).length ≤ k) →
      CounterPrograms.value countWord = 3*clauses.length →
      generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
        (SparseCode.distanceDenom clauses.length B) = seed :: rest →
      bits ∈ seed :: rest → 0 < B → clauses.length ≤ n*B → B ≤ L n^q →
      round ≤ HashSelect.loopCap n clauses.length →
      BinaryArithmetic.toNat nb = n → BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1 →
      let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
      let decode := rawDecode clauses.length countWord.length hm
      let rows := trial decode score seed rest initial round bits
      let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
      let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
      let x := measuredParameterInput scopes mask clauses.length k
      Guard x ∧ passes x = true ∧ dispatch x = .sparse ∧
        x.freeCount ≤ n ∧ n ≤ 2*x.freeCount ∧
        x.factors ≤ 4*n+HashSelect.loopCap n clauses.length+2 ∧
        x.occurrence ≤ L x.freeCount^(resourceExponent q+1) ∧
        x.arity ≤ L x.freeCount^(resourceExponent q+1) := by
  filter_upwards [eventually_supplied_trial_guards k q] with n hn B t d round clauses hm
    codes s Q countWord score seed rest bits mark nb tb hcodes hcount hfamily hbits hB hmb hBL hr hnb htb
  let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
  have hw : 3*clauses.length ≤ 2^countWord.length :=
    (HashFamilyPayload.countWord_width_sufficient countWord hcount).le
  have hf : generatedPayloads (HashFamilyPayload.alphabet clauses.length countWord.length)
      (SparseCode.distanceDenom clauses.length B) = seed :: rest := by
    simpa only [HashFamilyPayload.alphabetWords_eq countWord hcount] using hfamily
  have hlength : ∀ p ∈ seed :: rest,
      (rawDecode clauses.length countWord.length hm p).length ≤
        SparseCode.distanceDenom clauses.length B := by
    intro p hp
    rw [rawDecode_generated_length (depth := SparseCode.distanceDenom clauses.length B)
      hm hw p (by simpa [hf] using hp)]
  have hdecode := initialPayloads_decode hm hw (CodeRowsProgram.serializedRows clauses.length s Q)
  exact hn B t d round clauses codes s Q (rawDecode clauses.length countWord.length hm)
    score seed rest initial bits mark nb tb hcodes hdecode hlength hbits hm hB hmb hBL hr hnb htb

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
