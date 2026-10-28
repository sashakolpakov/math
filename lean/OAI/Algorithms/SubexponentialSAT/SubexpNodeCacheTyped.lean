import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheStage
import OAI.Algorithms.SubexponentialSAT.SubexpOriginCacheSemantics

namespace OAI.Algorithms

/-!
# Actual row coefficients to the typed current-node Taylor cache

The row master is the output of source-row evaluation and coefficient
lifting. Its stored length is R+1, independently of the requested Taylor
count N. The exact output bytes are the input consumed by origin extraction.
-/

namespace SubexponentialSAT.SubexpNodeCacheTyped

open BitProgram StructuredCalls SubexpLiftRing
open SubexpNodeCacheStage (Data localState)

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)

def rows (R : ℕ) (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :=
  es.map (List.map (SubexpTaylorRowCorrectness.sourceOutput p μ source R))

@[simp] theorem rows_length (R : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    (rows p μ source R es).length = es.length := by
  simp [rows]

theorem rows_width (R C : ℕ) (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C) :
    ∀ incidence ∈ rows p μ source R es, incidence.length ≤ C := by
  intro incidence hi
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hi
  simpa only [List.length_map] using hC old ho

theorem row_length (R : ℕ) (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    ∀ incidence ∈ rows p μ source R es, ∀ row ∈ incidence, row.length ≤ R + 1 := by
  intro incidence hi row hr
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hi
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact (SubexpTaylorRowCorrectness.sourceOutput_length p μ source R e).le

variable (M : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)

theorem cache_bytes (R N : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
        (SubexpTaylorCacheMap.caches p μ M reduction theta N (rows p μ source R es)) =
      SubexpOriginCacheSemantics.taylorBytes p μ source M reduction theta R N es := by
  rw [SubexpTaylorCacheMap.encoded_caches]
  unfold rows SubexpOriginCacheSemantics.taylorBytes
  rw [SubexpTaylorCacheMap.encodeList_map_eq]
  apply congrArg (fun encode => Encoding.encodeList encode es)
  funext incidence
  change Encoding.encodeList _
    (incidence.map (SubexpTaylorRowCorrectness.sourceOutput p μ source R)) = _
  rw [SubexpTaylorCacheMap.encodeList_map_eq]
  rfl

/-- The complete physical cache stage receives the actual lifted source-row
master and emits the exact typed cache used by the next arithmetic stage. -/
theorem command_eval (hμ : 0 < μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (R N C : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C)
    (d : Data) (h0 : d.stacks 0 = [])
    (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = [])
    (hi : SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ M reduction theta width blockWidth) N
        (localState (SubexpNodeCacheSetup.prepared d)))
    (hm : d.stacks 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
      (rows p μ source R es))
    (h102 : d.stacks 102 = []) (h103 : d.stacks 103 = [])
    (h104 : d.stacks 104 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpNodeCacheSetup.prepareCost d +
      SubexpTaylorCacheMap.tableBudget es.length C (R + 1) N (baseWidth p μ),
      ∃ out : Data, Eval SubexpNodeCacheStage.command n d out ∧
      out.stacks = Function.update (SubexpNodeCacheSetup.preparedStacks d.stacks) 102
        (SubexpOriginCacheSemantics.taylorBytes p μ source M reduction theta R N es) := by
  simpa only [rows_length, cache_bytes] using
    SubexpNodeCacheStage.command_eval p μ M hμ reduction theta width blockWidth hw hblock
      N C (R + 1) (rows p μ source R es) (rows_width p μ source R C es hC)
      (row_length p μ source R es) d h0 h100 h101 h66 h73 h74 h81 hi hm h102 h103 h104 h108

end SubexponentialSAT.SubexpNodeCacheTyped

end OAI.Algorithms
