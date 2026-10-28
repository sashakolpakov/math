import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputInstall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLabels

namespace OAI.Algorithms

/-! The saved native plan stream is exactly the layout's typed word-address
stream, in the native incidence enumeration order. No conversion is required. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ}

def address (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) : Fin words.length × Fin words.length :=
  (⟨(Semantics.owner scopes n mask hm i).val, by
      have h := (Semantics.owner scopes n mask hm i).isLt
      omega⟩,
   ⟨n + (Semantics.factor scopes n mask hm i).val, by
      have h := (Semantics.factor scopes n mask hm i).isLt
      omega⟩)

@[simp] theorem head_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) :
    (address scopes n mask hm words hw i).1.val =
      ((Semantics.nativeEntries scopes mask).get i).1 := rfl

@[simp] theorem factor_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask)
    (i : Semantics.Incidences scopes mask) :
    (address scopes n mask hm words hw i).2.val =
      n + ((Semantics.nativeEntries scopes mask).get i).2 := rfl

/-- Equality in the actual native list order, including repeated plans. -/
theorem labelPlans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask) :
    LayoutProgram.labelPlans words (address scopes n mask hm words hw) =
      Install.plans scopes n mask := by
  change LayoutProgram.labelPlans words (address scopes n mask hm words hw) =
    Loop.plans scopes n 0 scopes.length mask
  rw [← Semantics.incidencePlans_eq scopes n mask hm]
  unfold LayoutProgram.labelPlans PackingIncidenceProgram.incidencePlans
  apply List.map_congr_left
  intro i _
  rw [Semantics.incidencePlan_eq]
  rfl

/-- The physically saved plan bytes are already the layout frontend input. -/
theorem planBytes_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (words : List (Word r Q))
    (hw : words.length = n + Semantics.factorCount scopes mask) :
    ProgramEncoding.encodeRecords
      ((LayoutProgram.labelPlans words (address scopes n mask hm words hw)).map
        PackingVertexLabels.planPayload) =
    ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) := by
  rw [labelPlans_eq]
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Address

end OAI.Algorithms
