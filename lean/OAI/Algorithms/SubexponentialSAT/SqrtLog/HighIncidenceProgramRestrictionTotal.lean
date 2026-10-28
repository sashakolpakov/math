import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRestriction

namespace OAI.Algorithms

/-! Every correctly sized pair of branch streams is accepted by the actual
merge program, and the resulting original-coordinate assignment is unique. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev highCount := Subexp.PaddedCompletion.trueCount

def merge : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | true :: mask, high, low => high.headD false :: merge mask high.tail low
  | false :: mask, high, low => low.headD false :: merge mask high low.tail

theorem merge_spec (mask high low : List Bool)
    (hh : high.length = highCount mask)
    (hs : high.length + low.length = mask.length) :
    (merge mask high low).length = mask.length ∧
    selected true mask (merge mask high low) = high ∧
    selected false mask (merge mask high low) = low := by
  induction mask generalizing high low with
  | nil =>
      have hhigh : high = [] := List.eq_nil_of_length_eq_zero (by simpa [highCount, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful] using hh)
      have hlow : low = [] := List.eq_nil_of_length_eq_zero (by simpa [hhigh] using hs)
      simp [hhigh, hlow, merge, selected]
  | cons b mask ih =>
      cases b with
      | false =>
          have hh' : high.length = highCount mask := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases low with
          | nil =>
              have hb : highCount mask ≤ mask.length := by
                exact List.length_filter_le _ _
              simp only [List.length_nil, List.length_cons] at hs
              omega
          | cons x low =>
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh' hs'
              simp [merge, selected, hlen, hhigh, hlow]
      | true =>
          have hh' : high.length = highCount mask + 1 := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases high with
          | nil => simp at hh'
          | cons x high =>
              have hh'' : high.length = highCount mask := by simpa using hh'
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh'' hs'
              simp [merge, selected, hlen, hhigh, hlow]

/-- The physical input streams are arbitrary, subject only to their lengths;
there is no supplied full assignment or unimplemented reconstruction oracle. -/
theorem all_pairs_run (regs : Fin 4 → Bool) (mask high low out : List Bool)
    (hh : high.length = highCount mask)
    (hs : high.length + low.length = mask.length) :
    ∃ rf, RunsIn program (5 * mask.length + 3)
      ((state regs mask high low out).withPC (some program.entry))
      ((state rf [] [] [] ((merge mask high low).reverse ++ out)).withPC none) := by
  obtain ⟨hlen, hhigh, hlow⟩ := merge_spec mask high low hh hs
  simpa only [hhigh, hlow] using program_runsIn regs mask (merge mask high low) out hlen.symm

theorem merge_unique (mask high low xs : List Bool)
    (hh : high.length = highCount mask)
    (hs : high.length + low.length = mask.length)
    (hx : xs.length = mask.length)
    (hxhigh : selected true mask xs = high)
    (hxlow : selected false mask xs = low) : merge mask high low = xs := by
  obtain ⟨hlen, hhigh, hlow⟩ := merge_spec mask high low hh hs
  exact selected_pair_injective mask _ _ hlen.symm hx.symm
    (hhigh.trans hxhigh.symm) (hlow.trans hxlow.symm)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
