import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls
open Subexp.IncidencePlanSpec

theorem indices_length_le (scopes : List (List ℕ)) (e v : ℕ) :
    (indices scopes e v).length ≤ e * (2 * e + 2) := by
  have hp : (scopes.take e).length ≤ e := List.length_take_le e scopes
  have hi := SubexpIncidencePlanScan.indexPrefix_length_le
    (incidenceFrom v 0 (scopes.take e)).reverse e (by
      intro j hj
      have h := incidenceFrom_bounds v 0 j (scopes.take e) (by simpa using hj)
      omega)
  have hc := SubexpIncidencePlanScan.incidenceFrom_length_le v 0 (scopes.take e)
  simp only [List.length_reverse] at hi
  exact hi.trans (Nat.mul_le_mul_right _ (hc.trans hp))

theorem budget_le (scopes : List (List ℕ)) (e v B : ℕ)
    (hl : (scopeBits scopes).length ≤ B) (he : e ≤ B) (hv : v ≤ B) :
    budget scopes e v ≤ 1000 * (B + 1)^2 := by
  have hp : (scopes.take e).length ≤ B := (List.length_take_le e scopes).trans he
  have hlen := (prefix_length_le scopes e).trans hl
  have hs := SubexpIncidencePlanScan.scanBudget_le v 0 (scopes.take e)
  have hs' : SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) ≤
      (144 * B + 308) * B := hs.trans (Nat.mul_le_mul (by omega) hlen)
  have hi := (indices_length_le scopes e v).trans
    (Nat.mul_le_mul he (by omega : 2 * e + 2 ≤ 2 * B + 2))
  dsimp [budget]
  nlinarith

/-- One fixed quadratic bound in the actual input word lengths. -/
theorem program_runs_polynomial (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (e v : ℕ) (he : e ≤ scopes.length) :
    ∃ rf, RunsIn program (1000 * ((scopeBits scopes).length + e + v + 1)^2)
      ((idle regs scopes e v []).withPC (some program.entry))
      ((idle rf scopes e v (unary (degree scopes e v + 1))).withPC none) := by
  obtain ⟨rf, h⟩ := program_run regs scopes e v he
  exact ⟨rf, h.mono (budget_le scopes e v
    ((scopeBits scopes).length + e + v) (by omega) (by omega) (by omega))⟩

theorem prefix_rank (scopes : List (List ℕ)) (start e v : ℕ)
    (he : e < scopes.length) (hv : v ∈ scopes[e]) :
    (incidenceFrom v start scopes).idxOf (start + e) =
      (incidenceFrom v start (scopes.take e)).length := by
  induction scopes generalizing start e with
  | nil => simp at he
  | cons C Cs ih =>
      cases e with
      | zero =>
          have hm : v ∈ C := hv
          simp [incidenceFrom, hm]
      | succ e =>
          have he' : e < Cs.length := by simpa using he
          have hv' : v ∈ Cs[e] := hv
          have h := ih (start + 1) e he' hv'
          have hadd : start + (e + 1) = start + 1 + e := by omega
          by_cases hm : v ∈ C
          · rw [incidenceFrom, ite_eq_left hm, List.idxOf_cons_ne _ (by omega)]
            simpa [List.take_succ_cons, incidenceFrom, hm, hadd] using congrArg Nat.succ h
          · simpa [List.take_succ_cons, incidenceFrom, hm, hadd] using h

theorem degree_eq_rank (scopes : List (List ℕ)) (e v : ℕ)
    (he : e < scopes.length) (hv : v ∈ scopes[e]) :
    degree scopes e v = (incidentIndices scopes v).idxOf e := by
  simpa [degree, incidentIndices] using (prefix_rank scopes 0 e v he hv).symm

/-- The returned unary word is the one-based slot in the already fixed
encounter-order slot assignment used by the row and matrix constructors. -/
theorem degree_eq_slot (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (v : Fin D) (e : SlotAssignment.Incident (pattern D scopes) v) :
    degree scopes e.val.val v.val = (slots D Δ scopes hd v e).val := by
  rw [slots_val]
  exact degree_eq_rank scopes e.val.val v.val e.val.isLt
    ((mem_pattern_scope D scopes v e.val).mp e.property)

theorem primitive_run (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (e v : ℕ) (he : e ≤ scopes.length) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (1000 * ((scopeBits scopes).length + e + v + 1)^2))
      (primitiveCfg program ((idle regs scopes e v []).withPC (some program.entry)))
      (primitiveCfg program
        ((idle rf scopes e v (unary (degree scopes e v + 1))).withPC none)) := by
  obtain ⟨rf, n, hn, ht⟩ := program_runs_polynomial regs scopes e v he
  exact ⟨rf, (primitive_trace program ht).mono (Nat.mul_le_mul_left _ hn)⟩

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
