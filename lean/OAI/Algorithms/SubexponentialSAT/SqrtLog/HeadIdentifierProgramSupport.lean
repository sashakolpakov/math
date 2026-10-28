import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_low {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r)
    (i : Fin (count (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n)) :
    low (headOrder (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n i)=true := by
  exact ((typed_chosen_mem head low t g _).mp (List.getElem_mem i.isLt)).1

theorem headOrder_head {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r)
    (i : Fin (count (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n)) :
    head (headOrder (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n i) t=g := by
  exact ((typed_chosen_mem head low t g _).mp (List.getElem_mem i.isLt)).2

theorem headOrder_not_high {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (high : Fin n → Bool) (t : Fin Q) (g : Fin r)
    (i : Fin (count (predicate (headRows head) (lowBits (fun v => !high v)) (t.val*r+g.val)) n)) :
    high (headOrder (predicate (headRows head) (lowBits (fun v => !high v)) (t.val*r+g.val)) n i)=false := by
  simpa using headOrder_low head (fun v => !high v) t g i

/-- The physically emitted count is bounded by the exact low-head set.
The injection names the already emitted IDs; it performs no reindexing. -/
theorem count_le_card_low_head {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    count (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n ≤
      (Finset.univ.filter (fun v : Fin n => low v=true ∧ head v t=g)).card := by
  let p := predicate (headRows head) (lowBits low) (t.val*r+g.val)
  let S := Finset.univ.filter (fun v : Fin n => low v=true ∧ head v t=g)
  let f : Fin (count p n) → S := fun i => ⟨headOrder p n i,by
    have hi : (headOrder p n i).val ∈ chosenIds p n := List.getElem_mem i.isLt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (typed_chosen_mem head low t g (headOrder p n i)).mp hi⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact headOrder_injective p n (congrArg Subtype.val hij)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Scattering an actual all-true assignment over the emitted IDs yields
exactly the selection predicate in the original ambient coordinates. -/
theorem support_mask_at (p : ℕ → Bool) (n j : ℕ) (hj : j < n) :
    (HeadScatterProgram.mask n (chosenIds p n) (List.replicate (count p n) true))[j]? =
      some (p j) := by
  cases hp : p j with
  | false =>
      exact HeadScatterProgram.mask_outside n _ _ j (chosenIds_bound p n) hj
        (by simp [chosenIds,hp])
  | true =>
      have hm : j ∈ HeadScatterProgram.headIds (headOrder p n) := by
        rw [headOrder_ids]
        simp [chosenIds,hj,hp]
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      have he := HeadScatterProgram.typed_mask_head (headOrder p n)
        (headOrder_injective p n) (fun _ => true) i
      simpa only [headOrder_ids,HeadScatterProgram.headBits,List.ofFn_const,hi] using he

theorem support_mask_eq (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.mask n (chosenIds p n) (List.replicate (count p n) true) =
      List.ofFn (fun v : Fin n => p v.val) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [support_mask_at p n j hj]
    simp [hj]
  · rw [List.getElem?_eq_none (by
      rw [HeadScatterProgram.mask_length n _ _ (chosenIds_bound p n)]
      omega)]
    simp [hj]

theorem typed_support_mask_eq {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    HeadScatterProgram.mask n
      (chosenIds (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n)
      (List.replicate (count (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n) true) =
      List.ofFn (fun v : Fin n => low v && decide (head v t=g)) := by
  simpa only [typed_predicate] using
    support_mask_eq (predicate (headRows head) (lowBits low) (t.val*r+g.val)) n

/-- The support mask is computed by the existing fixed scatter machine.
The all-true input stream must itself be physically supplied by the caller. -/
theorem support_program_runsIn (regs : Fin 8 → Bool) (p : ℕ → Bool) (n : ℕ) :
    ∃ rf, RunsIn HeadScatterProgram.program (100*(n+1)*(count p n+1))
      ((HeadScatterProgram.input regs (chosenIds p n) (List.replicate (count p n) true) n).withPC
        (some HeadScatterProgram.program.entry))
      ((HeadScatterProgram.result rf (chosenIds p n) (List.replicate (count p n) true) n).withPC none) := by
  simpa only [count] using HeadScatterProgram.program_runsIn regs n (chosenIds p n)
    (List.replicate (count p n) true) (by simp [count]) (chosenIds_bound p n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
