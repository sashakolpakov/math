import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyHighMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsUniform

namespace OAI.Algorithms

/-! Uniform guard success for every actual supplied-code selector trial.
The score function is arbitrary, so the bound does not assume a successful
search trajectory.  The optional marked clause is included in the scopes. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafStatisticsProgram LeafParametersProgram

theorem eventually_supplied_trial_guards (k q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B t d round : ℕ) (clauses : List (List Bool))
        (codes : Fin clauses.length → List ℕ)
        (s : SparseCode.SuppliedShifts clauses.length B)
        (Q : SparseCode.SuppliedLocal clauses.length B)
        (decode : List Bool → List (Fin clauses.length × ZMod 3))
        (score : Records → List Bool → List Bool) (seed : List Bool)
        (rest initial : Records) (bits : List Bool) (mark : Option (Fin clauses.length))
        (nb tb : List Bool),
      (∀ i, (codes i).length ≤ k) →
      initial.map decode = CodeRowsProgram.serializedRows clauses.length s Q →
      (∀ b ∈ seed :: rest, (decode b).length ≤ SparseCode.distanceDenom clauses.length B) →
      bits ∈ seed :: rest → 0 < clauses.length → 0 < B →
      clauses.length ≤ n*B → B ≤ L n^q →
      round ≤ HashSelect.loopCap n clauses.length →
      BinaryArithmetic.toNat nb = n → BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1 →
      let rows := LeafScopeResourceBounds.trial decode score seed rest initial round bits
      let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
      let mask := LeafScopeResourceBounds.forwardMask scopes
        (HighIncidenceProgram.Prepare.cut scopes nb tb) n
      let x := measuredParameterInput scopes mask clauses.length k
      Guard x ∧ passes x = true ∧ dispatch x = .sparse ∧
        x.freeCount ≤ n ∧ n ≤ 2*x.freeCount ∧
        x.factors ≤ 4*n+HashSelect.loopCap n clauses.length+2 ∧
        x.occurrence ≤ L x.freeCount^(LeafScopeResourceBounds.resourceExponent q+1) ∧
        x.arity ≤ L x.freeCount^(LeafScopeResourceBounds.resourceExponent q+1) := by
  filter_upwards [eventually_forwardHighMask_guards
      (LeafScopeResourceBounds.statCoefficient k q) (LeafScopeResourceBounds.resourceExponent q),
    eventually_sparse_parameter_bounds q,
    Asymptotic.eventually_residual_polynomial (LeafScopeResourceBounds.statCoefficient k q)
      (LeafScopeResourceBounds.resourceExponent q), eventually_ge_atTop (1 : ℕ)]
    with n hguard hparameters hpoly hn B t d round clauses codes s Q decode score seed rest initial
      bits mark nb tb hcodes hdecode hfamily hbits hm hB hmb hBL hr hnb htb
  let rows := LeafScopeResourceBounds.trial decode score seed rest initial round bits
  let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
  let mask := LeafScopeResourceBounds.forwardMask scopes
    (HighIncidenceProgram.Prepare.cut scopes nb tb) n
  have hsize := (hparameters clauses.length B hmb hBL).1
  have hstats := LeafScopeResourceBounds.supplied_trial_measured n B t d k q round
    clauses codes hcodes s Q decode score seed rest initial hdecode hfamily bits hbits mark
    (by omega) hm hB hmb hBL hsize hr nb tb hnb htb
  change (measured scopes mask).occurrence ≤ _ ∧ _ at hstats
  obtain ⟨hocc,har,hfac,_,_,hnd,hlen⟩ := hstats
  have heq : mask = forwardHighMask scopes n (Nat.sqrt (L n)+1) := by
    dsimp [mask, LeafScopeResourceBounds.forwardMask, forwardHighMask,
      HighIncidenceProgram.Prepare.cut, HighIncidenceProgram.Prepare.mass]
    rw [hnb,htb]
  have hg := hguard scopes clauses.length k hm hnd
  rw [← heq] at hg
  have hG := hg hocc har
  have hfree : (measured scopes mask).free ≤ n :=
    (free_le_ambient scopes mask).trans_eq hlen
  have hhalf : n ≤ 2*(measured scopes mask).free := by
    rw [heq]
    exact forwardHighMask_retains_half scopes n _ (by omega) (highThreshold_ge_two n)
  exact ⟨hG,(passes_eq_true _).2 hG,(dispatch_sparse_iff _).2 hG,hfree,hhalf,hfac,
    hpoly _ _ hhalf hocc, hpoly _ _ hhalf har⟩

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
