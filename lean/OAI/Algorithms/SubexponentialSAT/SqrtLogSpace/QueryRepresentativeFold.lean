import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

/-- Mathematical fold matching the visitor's decreasing physical head address. -/
def run (mask : ℕ → List Bool) (base : ℕ) : List (List Bool) → List Bool → List Bool
  | [], baseline => baseline
  | word :: rest, baseline => run mask base rest
      (merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + rest.length)) word)
        (mask (base + rest.length)) baseline)

theorem zeroMerge_length (mask word : List Bool) :
    (HighIncidenceProgram.Restriction.zeroMerge mask word).length = mask.length := by
  induction mask generalizing word with
  | nil => rfl
  | cons b mask ih => cases b <;> simp [HighIncidenceProgram.Restriction.zeroMerge,
      HighIncidenceProgram.Restriction.merge, ih]

theorem run_length (mask : ℕ → List Bool) (base n : ℕ)
    (words : List (List Bool)) (baseline : List Bool) (hb : baseline.length = n)
    (hm : ∀ i < words.length, (mask (base + i)).length = n) :
    (run mask base words baseline).length = n := by
  induction words generalizing baseline with
  | nil => exact hb
  | cons word rest ih =>
    apply ih
    · simp only [merge_length, zeroMerge_length]
      exact hm rest.length (by simp)
    · intro i hi
      exact hm i (by simp; omega)

theorem run_ofFn_reverse (mask : ℕ → List Bool) (base : ℕ) {r : ℕ}
    (words : Fin r → List Bool) (baseline : List Bool) :
    run mask base (List.ofFn words).reverse baseline =
      (List.finRange r).reverse.foldl (fun acc g =>
        merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + g.val)) (words g))
          (mask (base + g.val)) acc) baseline := by
  induction r generalizing baseline with
  | zero => simp [run]
  | succ r ih =>
    have hrange : List.finRange (r+1) =
        (List.finRange r).map Fin.castSucc ++ [Fin.last r] := by
      change List.ofFn (fun i : Fin (r+1) => i) = _
      rw [List.ofFn_succ', List.concat_eq_append]
      change List.ofFn (fun i : Fin r => i.castSucc) ++ [Fin.last r] =
        (List.ofFn (fun i : Fin r => i)).map Fin.castSucc ++ [Fin.last r]
      rw [List.map_ofFn]
      rfl
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, run,
      List.length_reverse, List.length_ofFn]
    rw [ih, hrange]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ← List.map_reverse, List.foldl_map, Fin.val_last]
    rfl

@[simp] theorem run_nil (mask : ℕ → List Bool) (base : ℕ) (baseline : List Bool) :
    run mask base [] baseline = baseline := rfl

@[simp] theorem run_cons (mask : ℕ → List Bool) (base : ℕ)
    (word : List Bool) (rest : List (List Bool)) (baseline : List Bool) :
    run mask base (word :: rest) baseline = run mask base rest
      (merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + rest.length)) word)
        (mask (base + rest.length)) baseline) := rfl

theorem foldl_selected_ofFn {n : ℕ} {G : Type*} (heads : List G)
    (mask current : G → Fin n → Bool) (baseline : Fin n → Bool) :
    heads.foldl (fun acc g => merge
        (HighIncidenceProgram.Restriction.zeroMerge (List.ofFn (mask g))
          (HighIncidenceProgram.Restriction.selected true (List.ofFn (mask g))
            (List.ofFn (current g)))) (List.ofFn (mask g)) acc) (List.ofFn baseline) =
      heads.foldl (fun acc g => merge (List.ofFn (current g)) (List.ofFn (mask g)) acc)
        (List.ofFn baseline) := by
  induction heads generalizing baseline with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, HighQueryAdapter.Overlay.overlay_ofFn, merge_ofFn]
    exact ih _

/-- The actual reversed frame order and decreasing address reconstruct every
free head in its original ambient coordinates. Fixed-high bits and neutral
empty heads are retained. -/
theorem representative_words {n r : ℕ} (mask : ℕ → List Bool) (base : ℕ)
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → Fin r)
    (reps : ∀ g, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
    (words : Fin r → List Bool) (current : Fin r → Fin n → Bool)
    (hmask : ∀ g : Fin r, mask (base + g.val) =
      List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
    (hwords : ∀ g : Fin r, words g = HighIncidenceProgram.Restriction.selected true
      (mask (base + g.val)) (List.ofFn (current g)))
    (hcurrent : ∀ g (v : Fin n) (hv : v ∉ H) (hg : head v = g),
      current g v = reps g ⟨⟨v,hv⟩,hg⟩) :
    run mask base (List.ofFn words).reverse
        (List.ofFn (HighIncidence.glue H high (fun _ => false))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps)) := by
  rw [run_ofFn_reverse]
  have hf : (fun (acc : List Bool) (g : Fin r) =>
      merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + g.val)) (words g))
        (mask (base + g.val)) acc) =
      (fun acc g => merge
        (HighIncidenceProgram.Restriction.zeroMerge
          (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
          (HighIncidenceProgram.Restriction.selected true
            (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
            (List.ofFn (current g))))
        (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g))) acc) := by
    funext acc g
    rw [hwords g, hmask g]
  rw [hf, foldl_selected_ofFn]
  exact HeadRepresentativeSemantics.representative_heads H high head reps
    (List.finRange r).reverse (fun g => by simp) current
    (fun g _ v hv hg => hcurrent g v hv hg)

/-- A suffix of the reversed frame list determines the original head address. -/
theorem reverse_word_address {r : ℕ} (words : Fin r → List Bool)
    (pre : List (List Bool)) (word : List Bool) (rest : List (List Bool))
    (h : (List.ofFn words).reverse = pre ++ word :: rest) :
    ∃ i : Fin r, i.val = rest.length ∧ words i = word := by
  have hlen : r = pre.length + (rest.length + 1) := by
    have hh := congrArg List.length h
    simpa only [List.length_reverse,List.length_ofFn,List.length_append,
      List.length_cons] using hh
  have hi : rest.length < r := by omega
  refine ⟨⟨rest.length,hi⟩,rfl,?_⟩
  have hr : List.ofFn words = rest.reverse ++ word :: pre.reverse := by
    have hh := congrArg List.reverse h
    simpa only [List.reverse_reverse,List.reverse_append,List.reverse_cons,
      List.append_assoc,List.singleton_append] using hh
  have he := congrArg (fun xs : List (List Bool) => xs[rest.length]?) hr
  rw [List.getElem?_append_right (by simp)] at he
  simpa only [List.getElem?_ofFn, dite_eq_left hi, List.length_reverse, Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq] using he

theorem reversed_word_shape {r : ℕ} (mask : ℕ → List Bool) (base : ℕ)
    (words : Fin r → List Bool)
    (hw : ∀ i : Fin r, (words i).length =
      HighIncidenceProgram.Restriction.highCount (mask (base + i.val)))
    (pre : List (List Bool)) (word : List Bool) (rest : List (List Bool))
    (h : (List.ofFn words).reverse = pre ++ word :: rest) :
    word.length = HighIncidenceProgram.Restriction.highCount (mask (base + rest.length)) := by
  obtain ⟨i,hi,he⟩ := reverse_word_address words pre word rest h
  simpa only [hi,he] using hw i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
