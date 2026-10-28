import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsReachable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsPolylog

namespace OAI.Algorithms

/-! Every reachable supplied-code selector trial, for every optional mark,
has the same ambient resource envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic HashSelectProgram LeafStatisticsProgram LeafStatisticsSemantics

/-- Neutral completion adds at most one incidence per ambient coordinate. -/
theorem measured_incidences_le (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).incidences ≤ slots scopes + mask.length := by
  have hres : HighIncidence.totalScope (residualScope scopes mask) ≤
      HighIncidence.totalScope (HighIncidenceProgram.suppliedScope mask.length scopes) := by
    apply Finset.sum_le_sum
    intro e _
    exact HighIncidence.card_remainingScope_le _ _ e
  have hcard : Fintype.card (Free mask) ≤ mask.length := by
    simp
  rw [measured, incidences_exact]
  exact (HighIncidence.totalScope_neutralScope_le _).trans
    (Nat.add_le_add (hres.trans (HighIncidenceProgram.suppliedScope_mass_le _ _)) hcard)

/-- This theorem is pointwise in `score`, `round`, the trial, the code choices,
and the mark. In particular no trajectory-dependent constant is hidden. -/
theorem supplied_trial_measured (n B t d k q round : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (s : SparseCode.SuppliedShifts clauses.length B)
    (Q : SparseCode.SuppliedLocal clauses.length B)
    (decode : List Bool → List (Fin clauses.length × ZMod 3))
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (hdecode : initial.map decode = CodeRowsProgram.serializedRows clauses.length s Q)
    (hfamily : ∀ bits ∈ seed :: rest, (decode bits).length ≤ SparseCode.distanceDenom clauses.length B)
    (bits : List Bool) (hb : bits ∈ seed :: rest) (mark : Option (Fin clauses.length))
    (hn : 0 < n) (hm : 0 < clauses.length) (hB : 0 < B) (hmb : clauses.length ≤ n * B)
    (hBL : B ≤ L n^q) (hsize : Nat.size clauses.length ≤ n)
    (hr : round ≤ HashSelect.loopCap n clauses.length)
    (nb tb : List Bool) (hnb : BinaryArithmetic.toNat nb = n)
    (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1) :
    let rows := trial decode score seed rest initial round bits
    let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
    let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
    (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
      statCoefficient k q * L n^resourceExponent q ∧
    scopes.length + (measured scopes mask).uncovered ≤ 4*n + HashSelect.loopCap n clauses.length+2 ∧
    slots scopes ≤ n*(massCoefficient k q*L n^(2*q+3)) ∧
    (measured scopes mask).incidences ≤ n*(massCoefficient k q*L n^(2*q+3)+1) ∧
    (∀ row ∈ scopes, row.Nodup) ∧ mask.length=n := by
  dsimp only
  let ss := HashScopeProgram.Complete.scopes t d codes (trial decode score seed rest initial round bits) mark
  obtain ⟨hlen,hs,ha⟩ := supplied_trial n B t d k round clauses codes hcodes s Q
    decode score seed rest initial hdecode hfamily bits hb mark hn hm hB hmb
  have hS : HighIncidenceProgram.Prepare.mass ss ≤
      (3*n*SparseCode.degreeBound clauses.length B+
        (HashSelect.loopCap n clauses.length+1)*SparseCode.distanceDenom clauses.length B+1)*k := by
    apply hs.trans
    apply Nat.mul_le_mul_right
    have hh := Nat.mul_le_mul_right (SparseCode.distanceDenom clauses.length B) (Nat.add_le_add_right hr 1)
    omega
  obtain ⟨hocc,har⟩ := measured_polylog n clauses.length B k q hn hmb hBL hsize ss nb tb hnb htb hS ha
  have hmass := raw_mass_polylog n clauses.length B k q hn hmb hBL hsize _ hS
  have hfac := measured_factors_le ss (forwardMask ss (HighIncidenceProgram.Prepare.cut ss nb tb) n)
  have hinc := measured_incidences_le ss (forwardMask ss (HighIncidenceProgram.Prepare.cut ss nb tb) n)
  rw [forwardMask_length] at hfac hinc
  refine ⟨hocc,har,?_,hmass,?_,scopes_nodup _ _ _ _ _,forwardMask_length _ _ _⟩
  · change ss.length ≤ _ at hlen
    change ss.length + (measured ss (forwardMask ss (HighIncidenceProgram.Prepare.cut ss nb tb) n)).uncovered ≤ _
    omega
  · calc
      _ ≤ slots ss + n := hinc
      _ ≤ n*(massCoefficient k q*L n^(2*q+3))+n := Nat.add_le_add_right hmass n
      _ = _ := by ring

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
