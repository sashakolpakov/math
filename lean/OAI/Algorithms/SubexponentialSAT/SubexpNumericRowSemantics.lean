import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingCanonicalSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.OrderedComputedSource

namespace OAI.Algorithms

/-!
# Generated rows for the actual numeric-factor layout

The packing is built from the actual assignment's first/tail and the
physical type enumeration. The node order is the selected quartic machine
order. Only individual raw inverse/negative/difference cache values and
the successful coefficient check remain inputs to the row interpretation.
The original LE factor-system transport is separate from this numeric
factor statement.
-/

noncomputable section

namespace SubexponentialSAT.SubexpNumericRowSemantics

open MulticolorTypes Subexp.ConstructivePacking Subexp.ComputedLayout
open SubexpSelectedConversions SubexpRepresentedRows SubexpRowInterpolation
open SubexpTaylorExecution SubexpLayoutSpec Subexp.RepresentedNodeOrder

variable {D p k Δ r : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable (hr : 0 < r) (hQ : 0 < c.Q)
variable (first : Word r c.Q) (tail : List (Word r c.Q))

def packing (width : List Bool) (hwidth : width.length = c.Q * r) :
    PackingData (Fin D) (UniversalType r c.Q Δ) :=
  (Subexp.PackingCanonicalSpec.specWithWidth hr hQ scopes hd first tail width hwidth).packing

omit [Fact p.Prime] [NeZero r] in
/-- The physical packing specification uses exactly the same assignment,
vertex, seed and type orders as the computed layout. -/
theorem packing_eq (width : List Bool) (hwidth : width.length = c.Q * r) :
    packing scopes hd c hr hQ first tail width hwidth =
      packingWithWords (Subexp.IncidencePlanSpec.pattern D scopes)
        (Subexp.IncidencePlanSpec.slots D Δ scopes hd)
        (Subexp.OrderedComputedSource.finOrder D)
        (Subexp.PackingCanonicalSpec.types hr hQ Δ)
        (Subexp.OrderedComputedSource.seedOrder D scopes.length Δ) first tail := rfl

def nodes := nodesFor p (Subexp.ComputedMachineSource.nodeCount_eq c h4)

def nodeWords := nodeCodeFor p (Subexp.ComputedMachineSource.nodeCount_eq c h4)

def units : NodeUnits (fun j => (nodes c h4 j).val) := unitsForNodes (nodes c h4)

def cache (source : Prepared p 0) := nodeCache source.program (p ^ 4) (nodeWords c h4)

omit [NeZero r] in
theorem cache_node (source : Prepared p 0) (j : Fin c.Q) :
    source.residueRing.decode ((cache c h4 source).node j) = (nodes c h4 j).val :=
  nodeCodeFor_decode p (Subexp.ComputedMachineSource.nodeCount_eq c h4) source j

omit [NeZero r] in
theorem cache_inverse (source : Prepared p 0) (j : Fin c.Q) :
    source.residueRing.decode ((cache c h4 source).inverse j) = (units c h4).nodeInverse j := by
  exact Subexp.ComputedRowSource.cache_inverse source.residueRing (p ^ 4)
    (SubexpActualRing.extension_card p) (nodeWords c h4) (fun j => (nodes c h4 j).val)
    (cache_node c h4 source) (fun j => (nodes c h4 j).property) (units c h4) j

omit [NeZero r] in
theorem cache_difference (source : Prepared p 0) (j l : Fin c.Q) :
    source.residueRing.decode ((cache c h4 source).difference j l) =
      (units c h4).differenceInverse j l := by
  exact Subexp.ComputedRowSource.cache_difference source.residueRing (p ^ 4)
    (SubexpActualRing.extension_card p) (nodeWords c h4) (fun j => (nodes c h4 j).val)
    (cache_node c h4 source)
    (Subtype.val_injective.comp (nodes c h4).injective) (units c h4) j l

variable (hP : (Subexp.IncidencePlanSpec.pattern D scopes).Bounded k Δ)
variable (hsize : c.Dstar ≤ D)
variable (hthreshold : (Fintype.card (UniversalType r c.Q Δ) : ℚ)^3 *
  (1 + (Δ * k : ℕ)) ≤ τ^2 * c.Dstar)
variable (haNodup : (first :: tail).Nodup) (haFull : ∀ w, w ∈ first :: tail)
variable (A : ℕ)
variable (htail : Subexp.SpectralRank.normalizedTail r (c.Q - 1) A c.R ≤ τ / (Δ : ℚ))

/-- The exact numeric-factor layout exposed by the row bridge. -/
def layout : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p)
    (Subexp.IncidencePlanSpec.pattern D scopes) c :=
  layoutWithWordsOfTail (Subexp.IncidencePlanSpec.pattern D scopes) c hP
    (Subexp.ComputedSource.fin_size hsize) hthreshold
    (Subexp.ComputedMachineSource.extension_degree c h4) (nodes c h4)
    (Subexp.IncidencePlanSpec.slots D Δ scopes hd)
    (Subexp.OrderedComputedSource.finOrder D)
    (Subexp.PackingCanonicalSpec.types hr hQ Δ)
    (Subexp.OrderedComputedSource.seedOrder D scopes.length Δ)
    first tail haNodup haFull A htail

variable (width : List Bool) (hwidth : width.length = c.Q * r)
variable (source : Prepared p 0) (xs : List (ZMod p))
variable (inverse negative : Fin c.Q → List Bool)
variable (difference : Fin c.Q → Fin c.Q → List Bool)
variable (hinverse : ∀ j, SubexpRawRow.scalarDecode source (inverse j) =
  (units c h4).nodeInverse j)
variable (hnegative : ∀ j, SubexpRawRow.scalarDecode source (negative j) = -(nodes c h4 j).val)
variable (hdifference : ∀ j l, SubexpRawRow.scalarDecode source (difference j l) =
  (units c h4).differenceInverse j l)

omit [NeZero r] in
include hinverse in
private theorem inverse_cache (j : Fin c.Q) :
    SubexpRawRow.scalarDecode source (inverse j) =
      source.residueRing.decode ((cache c h4 source).inverse j) :=
  (hinverse j).trans (cache_inverse c h4 source j).symm

omit [NeZero r] in
include hnegative in
private theorem negative_cache (j : Fin c.Q) :
    SubexpRawRow.scalarDecode source (negative j) =
      source.residueRing.decode ((source.residueRing.negRun ((cache c h4 source).node j)).1) := by
  rw [source.residueRing.neg_correct, cache_node]
  exact hnegative j

omit [NeZero r] in
include hdifference in
private theorem difference_cache (j l : Fin c.Q) :
    SubexpRawRow.scalarDecode source (difference j l) =
      source.residueRing.decode ((cache c h4 source).difference j l) :=
  (hdifference j l).trans (cache_difference c h4 source j l).symm

include hP hsize hthreshold haNodup haFull htail hinverse hnegative hdifference in
/-- The actual expression at a numeric factor incidence is the row of the
same computed layout, not a row supplied by a caller. -/
theorem expressionFor_denote (hlength : xs.length = c.R)
    (hcheck : ∀ d : Fin c.R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    ((SubexpDenseRowTableSemantics.expressionFor source xs inverse negative difference
      (packing scopes hd c hr hQ first tail width hwidth) scopes hd e.val v.val w.val).map
        (SubexpRowSourceSemantics.denote source)).eval =
      (layout scopes hd c h4 hr hQ first tail hP hsize hthreshold haNodup haFull A htail).row
        e ⟨v, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w := by
  rw [SubexpDenseRowTableSemantics.expressionFor_at source xs inverse negative difference
    (packing scopes hd c hr hQ first tail width hwidth) scopes hd e v hv w]
  have h := SubexpGlobalRowSemantics.expressionAt_denote source xs inverse negative difference
    (cache c h4 source) (units c h4) (cache_node c h4 source)
    (cache_inverse c h4 source) (cache_difference c h4 source)
    (inverse_cache c h4 source inverse hinverse)
    (negative_cache c h4 source negative hnegative)
    (difference_cache c h4 source difference hdifference) A c.R hlength hcheck
    (packing scopes hd c hr hQ first tail width hwidth)
    (SubexpDenseRowProducer.slot scopes hd e v hv) v w
  refine h.trans ?_
  exact Subexp.ComputedRowSource.rowCode_decode
    (Subexp.IncidencePlanSpec.pattern D scopes) c hP (Subexp.ComputedSource.fin_size hsize)
    hthreshold (Subexp.ComputedMachineSource.extension_degree c h4) (nodes c h4)
    (Subexp.IncidencePlanSpec.slots D Δ scopes hd)
    (Subexp.OrderedComputedSource.finOrder D)
    (Subexp.PackingCanonicalSpec.types hr hQ Δ)
    (Subexp.OrderedComputedSource.seedOrder D scopes.length Δ)
    first tail haNodup haFull A htail source.residueRing (p ^ 4)
    (SubexpActualRing.extension_card p) (nodeWords c h4) (cache_node c h4 source)
    embedCode (embedCode_decode source) e
    ⟨v, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w

include hP hsize hthreshold haNodup haFull htail hinverse hnegative hdifference in
theorem expressionFor_degree (hlength : xs.length = c.R)
    (hcheck : ∀ d : Fin c.R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    ((SubexpDenseRowTableSemantics.expressionFor source xs inverse negative difference
      (packing scopes hd c hr hQ first tail width hwidth) scopes hd e.val v.val w.val).map
        (SubexpRowSourceSemantics.denote source)).eval.natDegree ≤ c.R := by
  rw [expressionFor_denote scopes hd c h4 hr hQ first tail hP hsize hthreshold
    haNodup haFull A htail width hwidth source xs inverse negative difference
    hinverse hnegative hdifference hlength hcheck e v hv w]
  exact (layout scopes hd c h4 hr hQ first tail hP hsize hthreshold haNodup haFull A htail).row_degree
    e ⟨v, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w

include hP hsize hthreshold haNodup haFull htail hinverse hnegative hdifference in
/-- The complete physical coefficient row is the selected coefficientwise
lift of that same numeric-layout row. -/
theorem rowCoefficients_denote (hlength : xs.length = c.R)
    (hcheck : ∀ d : Fin c.R,
      Subexp.CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    {N : ℕ} (target : Prepared p N)
    (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) (w : Fin D) :
    PolynomialAlgorithm.denote
      ((SubexpDenseRowSemantics.rowCoefficients source xs inverse negative difference
        (packing scopes hd c hr hQ first tail width hwidth) scopes hd (N + 1) e v hv w).map
          target.ring.decode) =
      SubexpExplicitLift.liftPolynomial
        (SubexpActualRing.sectionValue p (N + 1) (Nat.succ_pos N)) c.R
        ((layout scopes hd c h4 hr hQ first tail hP hsize hthreshold
          haNodup haFull A htail).row e
            ⟨v, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩ w) := by
  let expr := SubexpDenseRowTableSemantics.expressionFor source xs inverse negative difference
    (packing scopes hd c hr hQ first tail width hwidth) scopes hd e.val v.val w.val
  have he := expressionFor_denote scopes hd c h4 hr hQ first tail hP hsize hthreshold
    haNodup haFull A htail width hwidth source xs inverse negative difference
    hinverse hnegative hdifference hlength hcheck e v hv w
  have hdegree := expressionFor_degree scopes hd c h4 hr hQ first tail hP hsize hthreshold
    haNodup haFull A htail width hwidth source xs inverse negative difference
    hinverse hnegative hdifference hlength hcheck e v hv w
  have h := SubexpTaylorRowCorrectness.sourceOutput_denote p (N + 1) source (Nat.succ_pos N)
    c.R expr hdegree
  rw [show (expr.map (SubexpRowSourceSemantics.denote source)).eval = _ from he] at h
  have hs : SubexpDenseRowSemantics.rowCoefficients source xs inverse negative difference
      (packing scopes hd c hr hQ first tail width hwidth) scopes hd (N + 1) e v hv w =
      SubexpTaylorRowCorrectness.sourceOutput p (N + 1) source c.R expr := by
    dsimp only [expr]
    rw [SubexpDenseRowTableSemantics.expressionFor_at source xs inverse negative difference
      (packing scopes hd c hr hQ first tail width hwidth) scopes hd e v hv w]
    unfold SubexpDenseRowSemantics.rowCoefficients SubexpGlobalRowSemantics.coefficientsAt
      SubexpTaylorRowCorrectness.sourceOutput SubexpRowToTaylorCalls.evaluated
    rw [hlength]
  rw [hs]
  exact h

end SubexponentialSAT.SubexpNumericRowSemantics

end

end OAI.Algorithms
