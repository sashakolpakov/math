import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutData
import OAI.Algorithms.SubexponentialSAT.SubexpNumericRowCache

namespace OAI.Algorithms

/-! A genuine layout constructed from the Main program's actual choices.
The numerical feasibility hypotheses are separate from the computed data:
no layout, row polynomial, or desired coefficient output is supplied. -/

noncomputable section

namespace SubexponentialSAT.SubexpMainLayoutSemantics

open SubexpMainProgram SubexpLayoutSpec Subexp
open SubexpLayoutPorts (Allocation)
open MulticolorTypes

variable {p k Δ r : ℕ} {τ : ℚ}

/-- Fix the represented quartic index size literally while retaining all
numerical bounds of the supplied parameter record. -/
abbrev parameters (c : Parameters p k Δ r τ) (h4 : c.h = 4) : Parameters p k Δ r τ where
  h := 4
  Q := p^4 - 1
  R := c.R
  Dstar := c.Dstar
  p_odd := c.p_odd
  k_pos := c.k_pos
  delta_pos := c.delta_pos
  h_pos := by decide
  Q_eq := rfl
  degree_budget := by simpa only [c.Q_eq, h4] using c.degree_budget
  r_ge_two := c.r_ge_two
  tau_pos := c.tau_pos
  tau_le_half := c.tau_le_half

variable {er es D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {a middle out : MainState er es}
variable {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
variable {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
  p r Δ c.R D hr hQ scopes hd tables)
variable (hP : (IncidencePlanSpec.pattern D scopes).Bounded k Δ)
variable (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r (p^4 - 1) Δ) : ℚ)^3 *
  (1 + (Δ * k : ℕ)) ≤ τ^2 * c.Dstar)
variable (htail : SpectralRank.normalizedTail r (p^4 - 1 - 1)
  (TailInterval.intervalStart r (p^4 - 1) c.R) c.R ≤ τ / (Δ : ℚ))

def layout : Layout (E := SubexpActualRing.E p)
    (IncidencePlanSpec.pattern D scopes) (parameters c h4) :=
  SubexpNumericRowSemantics.layout scopes hd (parameters c h4) rfl hr hQ
    h.choices.first h.choices.tail hP hsize hthreshold h.choices.nodup h.choices.complete
    (TailInterval.intervalStart r (p^4 - 1) c.R) htail

theorem layout_node (i : Fin (p^4 - 1)) :
    (layout c h4 h hP hsize hthreshold htail).node i =
      (SubexpMachineNodeOrder.nodeEquiv p i).val := rfl

theorem packing_eq : h.choices.packing.packing =
    ComputedLayout.packingWithWords (IncidencePlanSpec.pattern D scopes)
      (IncidencePlanSpec.slots D Δ scopes hd)
      (OrderedComputedSource.finOrder D) (PackingCanonicalSpec.types hr hQ Δ)
      (OrderedComputedSource.seedOrder D scopes.length Δ)
      h.choices.first h.choices.tail := rfl

theorem expression_denote
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    ((SubexpDenseRowTableSemantics.expressionFor h.rows.cacheFacts.source
      (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
      h.rows.cacheFacts.difference h.choices.packing.packing scopes hd e.val v.val w.val).map
        (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval =
      (layout c h4 h hP hsize hthreshold htail).row
        e ⟨v, (IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w := by
  exact SubexpNumericRowSemantics.expressionFor_denote scopes hd (parameters c h4) rfl
    hr hQ h.choices.first h.choices.tail hP hsize hthreshold h.choices.nodup h.choices.complete
    (TailInterval.intervalStart r (p^4 - 1) c.R) htail
    h.choices.wordWidth h.choices.wordWidth_length h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference
    (SubexpNumericRowCache.inverse_decode (parameters c h4) rfl h.rows.cacheFacts)
    (SubexpNumericRowCache.negative_decode (parameters c h4) rfl h.rows.cacheFacts)
    (SubexpNumericRowCache.difference_decode (parameters c h4) rfl h.rows.cacheFacts)
    List.length_ofFn h.coefficient_check e v hv w

theorem row_coefficients_denote {N : ℕ} (target : SubexpSelectedConversions.Prepared p N)
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    PolynomialAlgorithm.denote
      ((SubexpDenseRowSemantics.rowCoefficients h.rows.cacheFacts.source
        (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
        h.rows.cacheFacts.difference h.choices.packing.packing scopes hd (N + 1) e v hv w).map
          target.ring.decode) =
      SubexpExplicitLift.liftPolynomial
        (SubexpActualRing.sectionValue p (N + 1) (Nat.succ_pos N)) c.R
        ((layout c h4 h hP hsize hthreshold htail).row e
          ⟨v, (IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w) := by
  exact SubexpNumericRowSemantics.rowCoefficients_denote scopes hd (parameters c h4) rfl
    hr hQ h.choices.first h.choices.tail hP hsize hthreshold h.choices.nodup h.choices.complete
    (TailInterval.intervalStart r (p^4 - 1) c.R) htail
    h.choices.wordWidth h.choices.wordWidth_length h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference
    (SubexpNumericRowCache.inverse_decode (parameters c h4) rfl h.rows.cacheFacts)
    (SubexpNumericRowCache.negative_decode (parameters c h4) rfl h.rows.cacheFacts)
    (SubexpNumericRowCache.difference_decode (parameters c h4) rfl h.rows.cacheFacts)
    List.length_ofFn h.coefficient_check target e v hv w

end SubexponentialSAT.SubexpMainLayoutSemantics

end

end OAI.Algorithms
