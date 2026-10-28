import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheTyped

namespace OAI.Algorithms

/-!
# The complete generated row table in the typed cache format

The expression list follows the physical traversal: outer factor order,
the emitted order within each scope, then increasing ambient coordinate.
No list of desired rows is supplied as an input equality.
-/

namespace SubexponentialSAT.SubexpDenseRowTableSemantics

open SubexpLiftRing SubexpQuarticRing SubexpSelectedConversions
open Subexp.ConstructivePacking MulticolorTypes
open SubexpDenseRowTableAssembly (Occurrence)
open SubexpTaylorCacheMap (encodeList_map_eq)

/-- The same nested traversal as `incidenceRows`, retaining expressions
instead of applying the physical row encoder. -/
def expressionRows {X : Type*} (expr : ℕ → ℕ → ℕ → X) (D : ℕ) :
    ℕ → List (List ℕ) → List (List X)
  | _, [] => []
  | e, scope :: scopes =>
      scope.map (fun v => (List.range D).map (expr e v)) ++
        expressionRows expr D (e + 1) scopes

theorem expressionRows_length {X : Type*} (expr : ℕ → ℕ → ℕ → X) (D e : ℕ)
    (scopes : List (List ℕ)) :
    (expressionRows expr D e scopes).length = (scopes.map List.length).sum := by
  induction scopes generalizing e with
  | nil => rfl
  | cons scope scopes ih => simp only [expressionRows, List.length_append,
      List.length_map, ih, List.map_cons, List.sum_cons]

theorem expressionRows_width {X : Type*} (expr : ℕ → ℕ → ℕ → X) (D e : ℕ)
    (scopes : List (List ℕ)) :
    ∀ row ∈ expressionRows expr D e scopes, row.length = D := by
  induction scopes generalizing e with
  | nil => simp only [expressionRows, List.not_mem_nil, false_implies, implies_true]
  | cons scope scopes ih =>
      intro row hr
      rcases List.mem_append.mp hr with hh | ht
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hh
        simp only [List.length_map, List.length_range]
      · exact ih (e + 1) row ht

private theorem occurrence_cons {scope : List ℕ} {scopes : List (List ℕ)}
    {e v : ℕ} (h : Occurrence scopes e v) : Occurrence (scope :: scopes) (e + 1) v := by
  obtain ⟨pre, C, rest, hs, he, hv⟩ := h
  refine ⟨scope :: pre, C, rest, ?_, ?_, hv⟩
  · simpa only [List.cons_append] using congrArg (List.cons scope) hs
  · simp only [List.length_cons]
    omega

private theorem incidenceRows_encode {X : Type*} (expr : ℕ → ℕ → ℕ → X)
    (encode : X → List Bool) (render : ℕ → ℕ → ℕ → List Bool) (D start : ℕ)
    (scopes : List (List ℕ))
    (hrow : ∀ e v w, Occurrence scopes e v → w < D →
      render (start + e) v w = encode (expr (start + e) v w)) :
    SubexpDenseRowTableProgram.incidenceRows render D start scopes =
      (expressionRows expr D start scopes).map (Encoding.encodeList encode) := by
  induction scopes generalizing start with
  | nil => rfl
  | cons scope scopes ih =>
      simp only [SubexpDenseRowTableProgram.incidenceRows, expressionRows,
        List.map_append, List.map_map, Function.comp_def]
      apply congrArg₂ List.append
      · apply List.map_congr_left
        intro v hv
        have hc : SubexpDenseRowTableProgram.coordinateRows render D start v =
            ((List.range D).map (expr start v)).map encode := by
          simp only [SubexpDenseRowTableProgram.coordinateRows, List.map_map, Function.comp_def]
          apply List.map_congr_left
          intro w hw
          have ho : Occurrence (scope :: scopes) 0 v :=
            ⟨[], scope, scopes, rfl, rfl, hv⟩
          simpa only [Nat.add_zero] using hrow 0 v w ho (List.mem_range.mp hw)
        rw [hc, encodeList_map_eq]
        all_goals rfl
      · apply ih (start + 1)
        intro e v w ho hw
        have h := hrow (e + 1) v w (occurrence_cons ho) hw
        have he : start + (e + 1) = (start + 1) + e := by omega
        simpa only [he] using h

private theorem encodeArray_eq_flatMap {B : ℕ} (a : List (Quad (Word B))) :
    SubexpCoefficientLiftArray.encodeArray a = a.flatMap SubexpTaylorRow.flat := by
  rw [List.flatMap_def]
  unfold SubexpCoefficientLiftArray.encodeArray
  apply congrArg List.flatten
  apply List.map_congr_left
  intro x _
  change SubexpFlatAdd.encode x = SubexpTaylorRow.flat x
  exact (SubexpHornerMachine.flat_eq_encode x).symm

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (xs : List (ZMod p))
variable (inverse negative : Fin Q → List Bool)
variable (difference : Fin Q → Fin Q → List Bool)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))
variable (scopes : List (List ℕ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The expression at actual counters. Invalid counters are irrelevant to
the traversal; a total zero expression keeps the definition executable. -/
def expressionFor (e v w : ℕ) : SubexpTaylorRowCorrectness.RowExpr p :=
  if he : e < scopes.length then
    if hv : v < D then
      if hw : w < D then
        if hm : v ∈ scopes.get ⟨e, he⟩ then
          SubexpGlobalRowSemantics.expressionAt source xs inverse negative difference P
            (SubexpDenseRowProducer.slot scopes hd ⟨e, he⟩ ⟨v, hv⟩ hm)
            ⟨v, hv⟩ ⟨w, hw⟩
        else SubexpGlobalRowConstants.expression source false
      else SubexpGlobalRowConstants.expression source false
    else SubexpGlobalRowConstants.expression source false
  else SubexpGlobalRowConstants.expression source false

theorem expressionFor_at (e : Fin scopes.length) (v : Fin D)
    (hv : v.val ∈ scopes.get e) (w : Fin D) :
    expressionFor source xs inverse negative difference P scopes hd e.val v.val w.val =
      SubexpGlobalRowSemantics.expressionAt source xs inverse negative difference P
        (SubexpDenseRowProducer.slot scopes hd e v hv) v w := by
  simp only [expressionFor, dite_eq_left e.isLt, dite_eq_left v.isLt, dite_eq_left w.isLt, dite_eq_left hv]

/-- Exactly one coordinate-expression list per emitted factor incidence. -/
def expressions : List (List (SubexpTaylorRowCorrectness.RowExpr p)) :=
  expressionRows (expressionFor source xs inverse negative difference P scopes hd) D 0 scopes

theorem expressions_length :
    (expressions source xs inverse negative difference P scopes hd).length =
      (scopes.map List.length).sum :=
  expressionRows_length _ _ _ _

theorem expressions_width :
    ∀ row ∈ expressions source xs inverse negative difference P scopes hd, row.length = D :=
  expressionRows_width _ _ _ _

theorem expressions_width_le :
    ∀ row ∈ expressions source xs inverse negative difference P scopes hd, row.length ≤ D := by
  intro row hr
  exact (expressions_width source xs inverse negative difference P scopes hd row hr).le

theorem render_eq_sourceOutput (μ : ℕ)
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D)
    (e v w : ℕ) (ho : Occurrence scopes e v) (hw : w < D) :
    SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd e v w =
      (SubexpTaylorRowCorrectness.sourceOutput p μ source xs.length
        (expressionFor source xs inverse negative difference P scopes hd e v w)).flatMap
          SubexpTaylorRow.flat := by
  have he := SubexpDenseRowTableAssembly.occurrence_factor_lt ho
  have hv := SubexpDenseRowTableContext.occurrence_vertex_lt hvalid ho
  have hm := SubexpDenseRowTableContext.occurrence_get ho
  rw [expressionFor_at source xs inverse negative difference P scopes hd
    ⟨e, he⟩ ⟨v, hv⟩ hm ⟨w, hw⟩]
  rw [SubexpDenseRowSemantics.render_eq_encode source xs inverse negative difference P scopes hd
    μ ⟨e, he⟩ ⟨v, hv⟩ hm ⟨w, hw⟩]
  change SubexpCoefficientLiftArray.encodeArray
    (SubexpTaylorRowCorrectness.sourceOutput p μ source xs.length _) = _
  exact encodeArray_eq_flatMap _

/-- The row master's complete physical bytes are exactly the input format
of `SubexpNodeCacheTyped`, with no assumed row-list identity. -/
theorem tableCode_eq_encodeRows (μ : ℕ)
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) :
    SubexpDenseRowTableProgram.tableCode
      (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D scopes =
      SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
        (SubexpNodeCacheTyped.rows p μ source xs.length
          (expressions source xs inverse negative difference P scopes hd)) := by
  have hr : ∀ e v w, Occurrence scopes e v → w < D →
      SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd (0 + e) v w =
        (SubexpTaylorRowCorrectness.sourceOutput p μ source xs.length
          (expressionFor source xs inverse negative difference P scopes hd (0 + e) v w)).flatMap
            SubexpTaylorRow.flat := by
    intro e v w ho hw
    simpa only [Nat.zero_add] using
      render_eq_sourceOutput source xs inverse negative difference P scopes hd μ hvalid e v w ho hw
  have h := incidenceRows_encode
    (expressionFor source xs inverse negative difference P scopes hd)
    (fun e => (SubexpTaylorRowCorrectness.sourceOutput p μ source xs.length e).flatMap
      SubexpTaylorRow.flat)
    (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd) D 0 scopes hr
  unfold SubexpDenseRowTableProgram.tableCode
  rw [h]
  simp only [expressions, SubexpNodeCacheTyped.rows, SubexpTaylorCacheControl.encodeRows,
    encodeList_map_eq, id_eq]

end SubexponentialSAT.SubexpDenseRowTableSemantics

end OAI.Algorithms
