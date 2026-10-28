import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableExecution

namespace OAI.Algorithms

/-! A single concrete row-service theorem suffices for the checked traversal.
The service is required only on actual scope occurrences and ambient
coordinates. All parser tails and accumulators remain framed runtime data. -/

namespace SubexponentialSAT.SubexpDenseRowTableAssembly

open BitProgram StructuredCalls SubexpDenseRowTableProgram

def varyingPorts : List (Fin 288) :=
  [87,257,258,259,260,261,262,263,266,267,268,269]

def SameContext (reference current : Store) : Prop :=
  ∀ i : Fin 288, i ∉ varyingPorts → current i = reference i

theorem sameContext_refl (s : Store) : SameContext s s := by
  intro i hi
  rfl

theorem sameContext_update {reference current : Store} (h : SameContext reference current)
    (j : Fin 288) (hj : j ∈ varyingPorts) (word : Word) :
    SameContext reference (Function.update current j word) := by
  intro i hi
  have hne : i ≠ j := by
    intro heq
    subst i
    exact hi hj
  simpa [hne] using h i hi

theorem sameContext_scopeFrame {reference initial current : Store}
    (h : SameContext reference initial) (hs : scopeFrame initial current) :
    SameContext reference current := by
  intro i hi
  have h268 : i ≠ 268 := by intro heq; subst i; exact hi (by decide)
  exact (hs i h268).trans (h i hi)

def Occurrence (scopes : List (List ℕ)) (e v : ℕ) : Prop :=
  ∃ pre C rest, scopes = pre ++ C :: rest ∧ e = pre.length ∧ v ∈ C

theorem occurrence_factor_lt {scopes : List (List ℕ)} {e v : ℕ}
    (h : Occurrence scopes e v) : e < scopes.length := by
  obtain ⟨pre, C, rest, rfl, rfl, _⟩ := h
  simp

/-- This is an actual execution of fixed finite code on a caller state.
It does not permit an atomic semantic row instruction or a runtime annotation.
The completed lookup/staging/evaluator composition must prove this property. -/
def RowService (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (reference : Store) (scopes : List (List ℕ)) (D : ℕ) : Prop :=
  ∀ e v w, Occurrence scopes e v → w < D → ∀ a : Data,
    SameContext reference a.stacks → a.stacks 261 = unary e →
    a.stacks 260 = unary v → a.stacks 262 = unary w → a.stacks 87 = [] →
    ∃ n ≤ cost e v w, ∃ regs,
      Eval row n a ⟨regs, Function.update a.stacks 87 (render e v w).reverse⟩

theorem sameContext_coordinate {reference : Store} (frame : Data)
    (h : SameContext reference frame.stacks) (regs : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    SameContext reference (coordinateState frame regs index remaining records output).stacks := by
  apply sameContext_update _ 266 (by decide)
  apply sameContext_update _ 263 (by decide)
  apply sameContext_update _ 262 (by decide)
  exact sameContext_update h 87 (by decide) output

theorem sameContext_vertex {reference : Store} (current : Store)
    (h : SameContext reference current) (regs : Fin 25 → Bool) (tail : Word) (v : ℕ) :
    SameContext reference
      (vertexReady (RecordPrograms.state scopePorts ⟨regs,current⟩
        false true false tail (Encoding.encodeNat v).reverse) v).stacks := by
  apply sameContext_update _ 260 (by decide)
  apply sameContext_update _ 260 (by decide)
  exact sameContext_update h 259 (by decide) tail

theorem coordinateState_updated (frame : Data) (regs regs' : Fin 25 → Bool)
    (index remaining : ℕ) (records : List Word) (output : Word) :
    (⟨regs', Function.update (coordinateState frame regs index remaining records []).stacks
      87 output⟩ : Data) = coordinateState frame regs' index remaining records output := by
  apply congrArg (StructuredProgram.State.mk regs')
  funext i
  by_cases hi : i = 87 <;> simp [coordinateState, Function.update_apply, hi]

theorem scopeRows_of_service (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (reference : Store) (scopes : List (List ℕ)) (D e : ℕ)
    (service : RowService row render cost reference scopes D)
    (initial : Store) (vertices : List ℕ)
    (hcontext : SameContext reference initial) (hcounter : initial 261 = unary e)
    (hoccurrence : ∀ v ∈ vertices, Occurrence scopes e v) :
    ScopeRows row (render e) (cost e) D initial vertices := by
  intro v hv current hs regs tail w hw remaining records runRegs
  let frame := vertexReady (RecordPrograms.state scopePorts ⟨regs,current⟩
    false true false tail (Encoding.encodeNat v).reverse) v
  let a := coordinateState frame runRegs w remaining records []
  have hc : SameContext reference a.stacks :=
    sameContext_coordinate frame
      (sameContext_vertex current (sameContext_scopeFrame hcontext hs) regs tail v)
      runRegs w remaining records []
  have he : a.stacks 261 = unary e := by
    have hcur := (hs 261 (by decide)).trans hcounter
    simpa [a, frame, coordinateState, vertexReady, RecordPrograms.state, scopePorts] using hcur
  have hv' : a.stacks 260 = unary v := by
    simp [a, frame, coordinateState, vertexReady]
  obtain ⟨n, hn, nextRegs, hrun⟩ := service e v w (hoccurrence v hv) hw a hc he hv'
    (by simp [a]) (by simp [a])
  refine ⟨n, hn, nextRegs, ?_⟩
  rw [show (⟨nextRegs, Function.update a.stacks 87 (render e v w).reverse⟩ : Data) =
      coordinateState frame nextRegs w remaining records (render e v w).reverse from
    coordinateState_updated frame runRegs nextRegs w remaining records _] at hrun
  exact hrun

theorem sameContext_factorScope {reference initial : Store}
    (h : SameContext reference initial) (regs : Fin 25 → Bool) (tail : Word) (vertices : List ℕ) :
    SameContext reference (factorScopeInput initial regs tail vertices).stacks := by
  apply sameContext_update _ 259 (by decide)
  apply sameContext_update _ 258 (by decide)
  apply sameContext_update _ 258 (by decide)
  exact sameContext_update h 257 (by decide) tail

theorem sameContext_factorStep {reference initial : Store}
    (h : SameContext reference initial) (render : ℕ → ℕ → ℕ → Word)
    (D : ℕ) (vertices : List ℕ) :
    SameContext reference (factorStep render D vertices initial) := by
  apply sameContext_update _ 268 (by decide)
  exact sameContext_update h 261 (by decide) _

theorem factorRows_of_service (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (reference : Store) (scopes : List (List ℕ)) (D : ℕ)
    (service : RowService row render cost reference scopes D)
    (pre remaining : List (List ℕ)) (initial : Store)
    (hscopes : scopes = pre ++ remaining)
    (hcontext : SameContext reference initial) (hcounter : initial 261 = unary pre.length) :
    FactorRows row render cost D initial remaining := by
  induction remaining generalizing pre initial with
  | nil => trivial
  | cons vertices rest ih =>
      constructor
      · intro regs tail
        have hlength : (initial 261).length = pre.length := by simp [hcounter, unary]
        rw [hlength]
        apply scopeRows_of_service row render cost reference scopes D pre.length service
          (factorScopeInput initial regs tail vertices).stacks vertices
          (sameContext_factorScope hcontext regs tail vertices)
        · simpa [factorScopeInput, transferred, factorInput, RecordPrograms.state, factorPorts,
            StackRoutines.transferStacks] using hcounter
        · intro v hv
          exact ⟨pre,vertices,rest,hscopes,rfl,hv⟩
      · apply ih (pre ++ [vertices]) (factorStep render D vertices initial)
        · simpa only [List.append_assoc, List.singleton_append] using hscopes
        · exact sameContext_factorStep hcontext render D vertices
        · simp [factorStep, hcounter, unary, List.replicate_succ]

theorem prepared_context (a : Data) : SameContext a.stacks (tablePrepared a).stacks := by
  apply sameContext_update _ 268 (by decide)
  exact sameContext_update (sameContext_refl _) 257 (by decide) _

/-- Final traversal application from a concrete row-service theorem. The
service is still an explicit execution obligation until the actual global
row implementation discharges it. -/
theorem program_runsIn_of_service (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (a : Data) (scopes : List (List ℕ)) (D : ℕ)
    (ha : TableReady a D scopes) (service : RowService row render cost a.stacks scopes D) :
    ∃ regs, RunsIn (program row) (tableRunCost a render cost D scopes + 1)
      (a.withPC (some (program row).entry))
      ((tableResult a regs render D scopes).withPC none) := by
  apply program_runsIn row render cost a D scopes ha
  apply factorRows_of_service row render cost a.stacks scopes D service [] scopes
    (tablePrepared a).stacks (by simp) (prepared_context a)
  have h261 : a.stacks 261 = [] := ha.2.2 _ (by decide)
  simp [tablePrepared, pushed, copied, StackRoutines.copyStacks, unary, h261]

end SubexponentialSAT.SubexpDenseRowTableAssembly

end OAI.Algorithms
