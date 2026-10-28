import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowEvaluation
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowSelection
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotBounds

namespace OAI.Algorithms

/-! The table traversal changes only its explicit parser/counter ports.
Consequently each row sees the same arithmetic context and physical input
masters. Scope occurrences also supply the typed incident-factor index used
by the actual prefix-slot routine. -/

namespace SubexponentialSAT.SubexpDenseRowTableContext

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpDenseRowTableAssembly SubexpGlobalRowSelection
open SubexpRowPostfixInterpreter (contextStore)

theorem varying_low {i : Fin 288} (hi : i.val < 256) (h : i ∈ varyingPorts) : i = 87 := by
  simp only [varyingPorts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem varying_lt270 {i : Fin 288} (h : i ∈ varyingPorts) : i.val < 270 := by
  simp only [varyingPorts, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem sameContext_low {reference current : Store} (h : SameContext reference current)
    (i : Fin 288) (hi : i.val < 256) (h87 : i ≠ 87) : current i = reference i := by
  apply h
  exact fun hm => h87 (varying_low hi hm)

theorem sameContext_highClean {a b : Data} (h : SameContext a.stacks b.stacks)
    (ha : HighClean a) : HighClean b := by
  intro i hi
  rw [h i (fun hm => by have := varying_lt270 hm; omega)]
  exact ha i hi

/-- Arithmetic data are identical below256. The one changing row-output
port is empty again at each invocation, as required by the traversal. -/
theorem evaluator_frame {reference current : Store} (h : SameContext reference current)
    (context : Fin 252 → Word)
    (hframe : ∀ i, reference (SubexpRowToTaylorCalls.stack i) = contextStore context i)
    (href : reference 87 = []) (hcur : current 87 = []) :
    ∀ i, current (SubexpRowToTaylorCalls.stack i) = contextStore context i := by
  intro i
  by_cases hi : i = 87
  · subst i
    change current 87 = contextStore context 87
    exact hcur.trans (href.symm.trans (hframe 87))
  · rw [sameContext_low h]
    · exact hframe i
    · exact i.isLt
    · intro heq
      apply hi
      apply Fin.ext
      exact congrArg (fun j : Fin 288 => j.val) heq

theorem master_scopes {reference current : Store} (h : SameContext reference current) :
    current 256 = reference 256 := h 256 (by decide)

theorem master_dimension {reference current : Store} (h : SameContext reference current) :
    current 264 = reference 264 := h 264 (by decide)

theorem master_lookup {reference current : Store} (h : SameContext reference current) :
    current 265 = reference 265 := h 265 (by decide)

theorem occurrence_vertex_lt {D : ℕ} {scopes : List (List ℕ)}
    (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) {e v : ℕ}
    (h : Occurrence scopes e v) : v < D := by
  obtain ⟨pre, C, rest, hs, he, hv⟩ := h
  apply hvalid C _ v hv
  rw [hs]
  simp

theorem occurrence_get {scopes : List (List ℕ)} {e v : ℕ}
    (h : Occurrence scopes e v) :
    v ∈ scopes.get ⟨e, occurrence_factor_lt h⟩ := by
  obtain ⟨pre, C, rest, hs, he, hv⟩ := h
  subst scopes e
  simpa using hv

/-- The source factor index is the actual counter value e, not a chosen
incident index with the same vertex. This preserves encounter-order slots. -/
def incident {D : ℕ} {scopes : List (List ℕ)} {e v : ℕ}
    (h : Occurrence scopes e v) (hv : v < D) :
    SlotAssignment.Incident (Subexp.IncidencePlanSpec.pattern D scopes) ⟨v,hv⟩ :=
  ⟨⟨e, occurrence_factor_lt h⟩,
    (Subexp.IncidencePlanSpec.mem_pattern_scope D scopes ⟨v,hv⟩ _).mpr (occurrence_get h)⟩

@[simp] theorem incident_val {D : ℕ} {scopes : List (List ℕ)} {e v : ℕ}
    (h : Occurrence scopes e v) (hv : v < D) : (incident h hv).val.val = e := rfl

end SubexponentialSAT.SubexpDenseRowTableContext

end OAI.Algorithms
