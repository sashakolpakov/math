import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowService
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowCode

namespace OAI.Algorithms

/-! The fixed complete dense-row table producer. Actual scope records select
the incidence, actual counters select coordinates, and the concrete global
row program computes every payload. No row-list or row-execution oracle is
an input to the final table theorem. -/

namespace SubexponentialSAT.SubexpDenseRowProducer

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpDenseRowTableAssembly SubexpDenseRowTableContext
  SubexpGlobalRowInputs SubexpGlobalRowSelection
open Subexp.ConstructivePacking
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore)

def command : Code := SubexpDenseRowTableProgram.command SubexpGlobalRowUniversal.command
def program := SubexpDenseRowTableProgram.program SubexpGlobalRowUniversal.command

theorem command_eq_code : command = SubexpDenseRowCode.command := rfl
theorem program_eq_code : program = SubexpDenseRowCode.program := rfl

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
variable (scopes : List (List ℕ))
  (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

def slot (e : Fin scopes.length) (v : Fin D) (hv : v.val ∈ scopes.get e) : Fin Δ :=
  Subexp.IncidencePlanSpec.slots D Δ scopes hd v
    ⟨e, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v e).mpr hv⟩

def render (e v w : ℕ) : Word :=
  if he : e < scopes.length then
    if hv : v < D then
      if hw : w < D then
        if hm : v ∈ scopes.get ⟨e,he⟩ then
          (SubexpGlobalRowService.outputAt μ source xs inverse negative difference P
            (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hm) ⟨v,hv⟩ ⟨w,hw⟩).reverse
        else []
      else []
    else []
  else []

noncomputable def rowCost (a : Data) (e v w : ℕ) : ℕ :=
  if he : e < scopes.length then
    if hv : v < D then
      if hw : w < D then
        if hm : v ∈ scopes.get ⟨e,he⟩ then
          SubexpGlobalRowService.costAt μ source xs inverse negative difference P scopes e a
            (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hm) ⟨v,hv⟩ ⟨w,hw⟩
        else 0
      else 0
    else 0
  else 0

theorem render_at (e v w : ℕ) (he : e < scopes.length) (hv : v < D) (hw : w < D)
    (hm : v ∈ scopes.get ⟨e,he⟩) :
    render μ source xs inverse negative difference P scopes hd e v w =
      (SubexpGlobalRowService.outputAt μ source xs inverse negative difference P
        (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hm) ⟨v,hv⟩ ⟨w,hw⟩).reverse := by
  simp only [render, dite_eq_left he, dite_eq_left hv, dite_eq_left hw, dite_eq_left hm]

theorem rowCost_at (a : Data) (e v w : ℕ) (he : e < scopes.length)
    (hv : v < D) (hw : w < D) (hm : v ∈ scopes.get ⟨e,he⟩) :
    rowCost μ source xs inverse negative difference P scopes hd a e v w =
      SubexpGlobalRowService.costAt μ source xs inverse negative difference P scopes e a
        (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hm) ⟨v,hv⟩ ⟨w,hw⟩ := by
  simp only [rowCost, dite_eq_left he, dite_eq_left hv, dite_eq_left hw, dite_eq_left hm]

variable (reference : Data)
variable (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D)
variable (h2 : (2 : ZMod p) ≠ 0) (hμ : 0 < μ)
variable (hm : Masters p r Q xs inverse negative difference reference)
variable (htable : reference.stacks 265 =
  SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
variable (hscopes : reference.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
variable (hclean : HighClean reference) (href87 : reference.stacks 87 = [])
variable (hzero : reference.stacks 131 = SubexpFlatAdd.encode source.zero)
variable (hone : reference.stacks 132 = SubexpFlatAdd.encode source.one)
variable (sw tw : Word) (frame : Fin 6 → Word) (context : Fin 252 → Word)
variable (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
  (xs.length + 1) sw frame context)
variable (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
variable (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
variable (hB : tw.length = baseWidth p μ)
variable (hf : ∀ j, reference.stacks (SubexpRowToTaylorCalls.stack j) = contextStore context j)

include hvalid h2 hμ hm htable hscopes hclean href87 hzero hone H hz h74 h87 hB hf

/-- The row-service obligation is proved from the concrete global program
and stored inputs. Arbitrary current parser tails remain framed. -/
theorem rowService :
    RowService SubexpGlobalRowUniversal.command
      (render μ source xs inverse negative difference P scopes hd)
      (rowCost μ source xs inverse negative difference P scopes hd reference)
      reference.stacks scopes D := by
  intro e v w hoc hw a hsame hfactor hsource htarget ha87
  have he : e < scopes.length := occurrence_factor_lt hoc
  have hv : v < D := occurrence_vertex_lt hvalid hoc
  have hmem : v ∈ scopes.get ⟨e,he⟩ := occurrence_get hoc
  let ei : SlotAssignment.Incident (Subexp.IncidencePlanSpec.pattern D scopes) (⟨v,hv⟩ : Fin D) :=
    ⟨⟨e,he⟩, (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes ⟨v,hv⟩ ⟨e,he⟩).mpr hmem⟩
  have hslot : SubexpIncidenceSlotProgram.degree scopes e v =
      (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hmem).val :=
    SubexpIncidenceSlotProgram.degree_eq_slot D Δ scopes hd ⟨v,hv⟩ ei
  have ham := Masters.of_sameContext p r Q xs inverse negative difference hm hsame
  have hatable := (master_lookup hsame).trans htable
  have hascopes := (master_scopes hsame).trans hscopes
  have haclean := sameContext_highClean hsame hclean
  have hazero := (sameContext_low hsame 131 (by decide) (by decide)).trans hzero
  have haone := (sameContext_low hsame 132 (by decide) (by decide)).trans hone
  have haf := evaluator_frame hsame context hf href87 ha87
  obtain ⟨n, hn, regs, hr⟩ := SubexpGlobalRowService.run_at μ source xs inverse negative difference P
    scopes e he.le (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hmem) ⟨v,hv⟩ ⟨w,hw⟩ hslot h2 hμ a
    ham hatable hascopes hfactor hsource htarget haclean hazero haone sw tw frame context H hz h74 h87 hB haf
  refine ⟨n, ?_, regs, ?_⟩
  · rw [rowCost_at μ source xs inverse negative difference P scopes hd reference e v w he hv hw hmem]
    rw [SubexpGlobalRowService.costAt_sameContext μ source xs inverse negative difference P
      scopes e reference a (slot scopes hd ⟨e,he⟩ ⟨v,hv⟩ hmem) ⟨v,hv⟩ ⟨w,hw⟩ hsame] at hn
    exact hn
  · rw [render_at μ source xs inverse negative difference P scopes hd e v w he hv hw hmem,
      List.reverse_reverse]
    exact hr

/-- The entire nested table is produced inside this one fixed finite
program from actual parameter, packing, and cache bytes. -/
theorem program_runsIn (hready : TableReady reference D scopes) :
    ∃ regs, RunsIn program
      (tableRunCost reference (render μ source xs inverse negative difference P scopes hd)
        (rowCost μ source xs inverse negative difference P scopes hd reference) D scopes + 1)
      (reference.withPC (some program.entry))
      ((tableResult reference regs (render μ source xs inverse negative difference P scopes hd) D scopes).withPC none) := by
  apply program_runsIn_of_service SubexpGlobalRowUniversal.command _ _ reference scopes D hready
  exact rowService μ source xs inverse negative difference P scopes hd reference hvalid h2 hμ hm htable
    hscopes hclean href87 hzero hone sw tw frame context H hz h74 h87 hB hf

theorem primitive_runsIn (hready : TableReady reference D scopes) :
    ∃ regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (tableRunCost reference (render μ source xs inverse negative difference P scopes hd)
          (rowCost μ source xs inverse negative difference P scopes hd reference) D scopes + 1))
      (primitiveCfg program (reference.withPC (some program.entry)))
      (primitiveCfg program
        ((tableResult reference regs (render μ source xs inverse negative difference P scopes hd) D scopes).withPC none)) := by
  obtain ⟨regs, hr⟩ := program_runsIn μ source xs inverse negative difference P scopes hd reference
    hvalid h2 hμ hm htable hscopes hclean href87 hzero hone sw tw frame context H hz h74 h87 hB hf hready
  exact ⟨regs, BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.SubexpDenseRowProducer

end OAI.Algorithms
