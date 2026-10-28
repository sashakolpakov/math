import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpJetAccumulator
import OAI.Algorithms.SubexponentialSAT.SubexpExecution

namespace OAI.Algorithms

/-!
# Reading the contents of the physical moment array

These lemmas identify a list update with its mathematical per-cell update.
They do not implement an array operation or assign a machine cost. The
physical read/add/replace program is verified in `SubexpJetCellProgram`.
-/

namespace SubexponentialSAT.SubexpMomentArray

open SymbolicCost SubexpSymbolicCost

section Contents

variable {C R : Type*} [Zero R]

def contents (decode : C → R) (cells : List C) (i : ℕ) : R :=
  (cells.map decode).getD i 0

theorem contents_getD (decode : C → R) (zero : C) (hz : decode zero = 0)
    (cells : List C) (i : ℕ) :
    contents decode cells i = decode (cells.getD i zero) := by
  simpa only [contents, hz] using List.getD_map cells zero decode (n := i)

theorem contents_set (decode : C → R) (cells : List C) (i : ℕ) (value : C)
    (hi : i < cells.length) :
    contents decode (cells.set i value) =
      Function.update (contents decode cells) i (decode value) := by
  funext j
  by_cases h : i = j
  · subst j
    rw [Function.update_self]
    unfold contents
    rw [List.map_set, List.getD_eq_getElem?_getD,
      List.getElem?_set_self (by simpa only [List.length_map] using hi)]
    rfl
  · rw [Function.update_of_ne (Ne.symm h)]
    simp only [contents, List.map_set, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne h]

theorem contents_replicate (decode : C → R) (zero : C) (hz : decode zero = 0)
    (n : ℕ) : contents decode (List.replicate n zero) = fun _ => 0 := by
  funext i
  simp only [contents, List.map_replicate, hz, List.getD_eq_getElem?_getD,
    List.getElem?_getD_replicate_default_eq]

theorem map_eq_range_contents (decode : C → R) (cells : List C) :
    cells.map decode = (List.range cells.length).map (contents decode cells) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < cells.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map, List.getElem_range]
    unfold contents
    rw [List.getD_eq_getElem (cells.map decode) 0
      (by simpa only [List.length_map] using h)]
    exact (List.getElem_map (f := decode) (l := cells) (i := i)).symm

end Contents

section Evaluation

private theorem map_map {L S T : Type*} (f : L → S) (g : S → T)
    (e : Algorithm.Expr L) :
    (e.map f).map g = e.map (fun x => g (f x)) := by
  induction e with
  | lit x => rfl
  | add e f he hf => simp only [Algorithm.Expr.map, he, hf]
  | mul e f he hf => simp only [Algorithm.Expr.map, he, hf]

variable {D : ℕ} {C R : Type*} [CommRing R]

/-- Changing only the complete retained-slot enumeration changes no
coefficient. This avoids imposing the old list order on the machine. -/
theorem programEval_coeff (ops : RepresentedRing C R) (slots : List (RawIndex D))
    (hn : slots.Nodup) (hs : ∀ a, a ∈ slots ↔ Retained D a)
    (e : Algorithm.Expr (CoeffList D C)) (a : RawIndex D) :
    coeff (decodeList ops (SubexpExecution.programEval ops.program slots e).1) a =
      coeff ((((e.map (decodeList ops)).map
        (Algorithm.Dense.ofRaw (Algorithm.retainedSlots D))).eval).coefficients) a := by
  have hm := SubexpExecution.programEval_denote ops slots hn hs e
  have hr := Algorithm.eval_retainedDense_denote (e.map (decodeList ops))
  simp only [map_map] at hr
  have hd := hm.trans hr.symm
  simpa only [map_map, polyCoeff_denote] using congrArg (fun P => polyCoeff P a) hd

theorem programEval_contribution (ops : RepresentedRing C R)
    (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ Retained D a)
    (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C))
    (q : SubexpExtractionJobs.Query D) :
    coeff (decodeList ops
      (SubexpExecution.programEval ops.program slots (source q.exponent)).1)
        (q.exponent, (q.u, q.z)) =
      SubexpExtractionJobs.contribution (fun a => (source a).map (decodeList ops)) q :=
  programEval_coeff ops slots hn hs (source q.exponent) (q.exponent, (q.u, q.z))

end Evaluation

end SubexponentialSAT.SubexpMomentArray

end OAI.Algorithms
