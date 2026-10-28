import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyGeneratedGuards

namespace OAI.Algorithms

/-! The final selected table is exactly the last winning trial.  This gives
the final unmarked count the same uniform guard certificate as trial calls;
no monotonicity of the recomputed high mask is needed. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafParametersProgram LeafScopeResourceBounds

theorem selected_succ_eq_trial {α : Type*} (decode : List Bool → List α)
    (score : Records → List Bool → List Bool) (seed : List Bool)
    (rest initial : Records) (round : ℕ) :
    (selected score seed rest initial (round+1)).map decode =
      trial decode score seed rest initial round
        (HashSelect.best (fun bits => BinaryArithmetic.toNat
          (score (selected score seed rest initial round) bits)) seed rest) := by
  simp only [selected, iter_succ_apply, payloadNext, trial]

theorem eventually_generated_selected_guards (k q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B t d : ℕ) (clauses : List (List Bool)) (hm : 0 < clauses.length)
        (codes : Fin clauses.length → List ℕ)
        (s : SparseCode.SuppliedShifts clauses.length B)
        (Q : SparseCode.SuppliedLocal clauses.length B)
        (countWord : List Bool) (score : Records → List Bool → List Bool)
        (seed : List Bool) (rest : Records)
        (mark : Option (Fin clauses.length)) (nb tb : List Bool),
      (∀ i, (codes i).length ≤ k) →
      CounterPrograms.value countWord = 3*clauses.length →
      generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
        (SparseCode.distanceDenom clauses.length B) = seed :: rest →
      0 < B → clauses.length ≤ n*B → B ≤ L n^q →
      BinaryArithmetic.toNat nb = n → BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1 →
      let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
      let decode := rawDecode clauses.length countWord.length hm
      let rows := (selected score seed rest initial (HashSelect.loopCap n clauses.length)).map decode
      let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
      let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
      let x := measuredParameterInput scopes mask clauses.length k
      Guard x ∧ passes x = true ∧ dispatch x = .sparse ∧
        x.freeCount ≤ n ∧ n ≤ 2*x.freeCount ∧
        x.factors ≤ 4*n+HashSelect.loopCap n clauses.length+2 ∧
        x.occurrence ≤ L x.freeCount^(resourceExponent q+1) ∧
        x.arity ≤ L x.freeCount^(resourceExponent q+1) := by
  filter_upwards [eventually_generated_trial_guards k q] with n hn B t d clauses hm
    codes s Q countWord score seed rest mark nb tb hcodes hcount hfamily hB hmb hBL hnb htb
  let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
  let decode := rawDecode clauses.length countWord.length hm
  let K := HashSelect.loopCap n clauses.length
  let winner := HashSelect.best (fun bits => BinaryArithmetic.toNat
    (score (selected score seed rest initial (K-1)) bits)) seed rest
  have hK : K-1+1=K := by dsimp [K,HashSelect.loopCap]; omega
  have heq : (selected score seed rest initial K).map decode =
      trial decode score seed rest initial (K-1) winner := by
    conv_lhs => rw [← hK]
    exact selected_succ_eq_trial decode score seed rest initial (K-1)
  have hg := hn B t d (K-1) clauses hm codes s Q countWord score seed rest winner mark nb tb
    hcodes hcount hfamily (HashSelect.best_mem _ seed rest) hB hmb hBL
    (Nat.sub_le _ _) hnb htb
  change Guard (measuredParameterInput _ _ _ _) ∧ _
  dsimp only [initial,decode,K] at heq hg
  simpa only [← heq] using hg

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
