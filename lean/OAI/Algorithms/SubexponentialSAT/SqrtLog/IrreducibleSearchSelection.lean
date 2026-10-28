import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

namespace OAI.Algorithms

/-! Exact first-success selection, including the existing chosen polynomial. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open SubexpEnumerationPayload SubexpTupleRefinement

theorem find_candidates_eq_coefficients {d : ℕ} (hd : 0 < d) :
    (candidates d).find? passes = some (coefficients d) := by
  have hv : (search d).1 = (candidates d).find? passes := by
    simp only [search, QuarticSearch.scan_value, evaluate_value]
  cases hs : (search d).1 with
  | none => exact False.elim (search_ne_none hd hs)
  | some c =>
      rw [← hv, hs]
      simp only [coefficients, hs, Option.getD_some]

theorem find_encoded_eq_coefficients {d : ℕ} (hd : 0 < d)
    (check : List Bool → Bool)
    (hcheck : ∀ c : Fin d → F, check (encodeTuple (scalarCode 3) c) = passes c) :
    ((candidates d).map (encodeTuple (scalarCode 3))).find? check =
      some (encodeTuple (scalarCode 3) (coefficients d)) := by
  rw [List.find?_map]
  have he : check ∘ encodeTuple (scalarCode 3) = (passes : (Fin d → F) → Bool) := by
    funext c
    exact hcheck c
  rw [he, find_candidates_eq_coefficients hd]
  rfl

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
