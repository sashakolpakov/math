import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionJobs

namespace OAI.Algorithms

/-!
# Accumulator invariant for the extraction-job machine

This file concerns the mathematical contents of the packed jet array.  The
runtime implementation is the fixed read/add/replace program; the functions
below express its per-cell invariant and do not stand in for machine steps.
-/

namespace SubexponentialSAT.SubexpJetAccumulator

open SubexpExtractionJobs

section FiniteFold

variable {α R : Type*} [AddCommMonoid R]

def addAt (index : α → ℕ) (value : α → R) (cells : ℕ → R) (a : α) : ℕ → R :=
  Function.update cells (index a) (cells (index a) + value a)

/-- A sequence of single-cell additions has the expected sum at every cell,
without an assumption about the order of jobs. -/
theorem fold_addAt (index : α → ℕ) (value : α → R) (as : List α)
    (cells : ℕ → R) (r : ℕ) :
    (as.foldl (addAt index value) cells) r =
      cells r + (as.map fun a => if index a = r then value a else 0).sum := by
  induction as generalizing cells with
  | nil => simp
  | cons a as ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      by_cases h : index a = r
      · unfold addAt
        rw [h]
        simp only [Function.update_self]
        exact add_assoc _ _ _
      · have hr : r ≠ index a := Ne.symm h
        simp [addAt, h, hr]

/-- An implementation that performs exactly the stated update at every step
satisfies the same invariant. This is the bridge used for concrete array
read/add/replace traces. -/
theorem fold_step_refinement {σ : Type*} (step : σ → α → σ)
    (contents : σ → ℕ → R) (index : α → ℕ) (value : α → R)
    (hstep : ∀ s a, contents (step s a) = addAt index value (contents s) a)
    (as : List α) (s : σ) (r : ℕ) :
    contents (as.foldl step s) r =
      contents s r + (as.map fun a => if index a = r then value a else 0).sum := by
  have hfold : contents (as.foldl step s) = as.foldl (addAt index value) (contents s) := by
    induction as generalizing s with
    | nil => rfl
    | cons a as ih =>
        simp only [List.foldl_cons, ih, hstep]
  rw [hfold, fold_addAt]

theorem sum_eq_of_perm (index : α → ℕ) (value : α → R)
    {as bs : List α} (h : as.Perm bs) (r : ℕ) :
    (as.map fun a => if index a = r then value a else 0).sum =
      (bs.map fun a => if index a = r then value a else 0).sum :=
  (h.map _).sum_eq

end FiniteFold

section Jet

variable {D : ℕ} {R : Type*} [CommSemiring R]

/-- The per-cell invariant identifies the machine's eventual array with the
previous verified jet algorithm. All starting cells are zero. -/
theorem queries_fold_eq_rawJet
    (program : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D R)) :
    (List.range D).map (fun r =>
      ((queries D).foldl (addAt Query.z (contribution program)) (fun _ => 0)) r) =
      Algorithm.executeRawJet program := by
  simp only [fold_addAt, zero_add]
  exact jobs_sum_eq_rawJet program

/-- Job generators may reverse or permute the retained-exponent and U/Z
loops. The output remains unchanged because each contribution is added. -/
theorem permuted_queries_fold_eq_rawJet
    (program : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D R))
    (qs : List (Query D)) (hqs : qs.Perm (queries D)) :
    (List.range D).map (fun r =>
      (qs.foldl (addAt Query.z (contribution program)) (fun _ => 0)) r) =
      Algorithm.executeRawJet program := by
  rw [← queries_fold_eq_rawJet program]
  apply List.map_congr_left
  intro r _
  simp only [fold_addAt, zero_add]
  exact sum_eq_of_perm Query.z (contribution program) hqs r

end Jet

end SubexponentialSAT.SubexpJetAccumulator

end OAI.Algorithms
