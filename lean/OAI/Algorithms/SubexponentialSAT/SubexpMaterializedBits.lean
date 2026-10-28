import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeMaterializer
import OAI.Algorithms.SubexponentialSAT.SubexpClauseRowProgram
import OAI.Algorithms.SubexponentialSAT.BooleanPackingLE

namespace OAI.Algorithms

/-!
# Indexed bits of the concretely materialized candidate

The scope program writes little-endian label bits into a uniform chunk array.
These lemmas connect its list specification to the finite assignment read by
the actual clause evaluator, including the final `take n` operation.
-/

namespace SubexponentialSAT.SubexpMaterializedBits

open SubexpScopeMaterializer SubexpFactorProgram

theorem allZero_iff_forall_mem (word : List Bool) :
    allZero word = true ↔ ∀ bit ∈ word, bit = false := by
  induction word with
  | nil => simp [allZero]
  | cons bit word ih => cases bit <;> simp [allZero, ih]

theorem allZero_iff_getElem? (word : List Bool) :
    allZero word = true ↔ ∀ (i : ℕ) (bit : Bool), word[i]? = some bit → bit = false := by
  rw [allZero_iff_forall_mem]
  constructor
  · intro h i bit hi
    exact h bit (List.mem_of_getElem? hi)
  · intro h bit hb
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
    exact h i bit hi

theorem allZero_drop_getElem? (word : List Bool) (cutoff i : ℕ) (bit : Bool)
    (hz : allZero (word.drop cutoff) = true) (hi : cutoff ≤ i)
    (hget : word[i]? = some bit) : bit = false := by
  apply (allZero_iff_getElem? (word.drop cutoff)).mp hz (i - cutoff) bit
  simpa only [List.getElem?_drop, Nat.add_sub_of_le hi] using hget

theorem allZero_append (xs ys : List Bool) :
    allZero (xs ++ ys) = (allZero xs && allZero ys) := by
  induction xs with
  | nil => simp [allZero]
  | cons bit xs ih => simp [allZero, ih, Bool.and_assoc]

theorem allZero_sublist {xs ys : List Bool} (hsub : xs.Sublist ys)
    (hz : allZero ys = true) : allZero xs = true := by
  apply (allZero_iff_forall_mem xs).mpr
  intro bit hb
  exact (allZero_iff_forall_mem ys).mp hz bit (hsub.subset hb)

theorem allZero_replicate_false (length : ℕ) :
    allZero (List.replicate length false) = true := by
  induction length with
  | zero => rfl
  | succ length ih => simpa [List.replicate_succ, allZero] using ih

theorem allZero_drop_replicate_false (length cutoff : ℕ) :
    allZero ((List.replicate length false).drop cutoff) = true :=
  allZero_sublist (List.drop_sublist _ _) (allZero_replicate_false length)

theorem allZero_drop_of_lt_pow (word : List Bool) (b cutoff : ℕ)
    (hvalue : BinaryArithmetic.toNat word < 2 ^ b) (hcut : b ≤ cutoff) :
    allZero (word.drop cutoff) = true := by
  by_cases hb : b ≤ word.length
  · have hz : allZero (word.drop b) = true := by
      apply (unary_validity_iff (word.take b) (word.drop b)).mpr
      simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hb] using hvalue
    exact allZero_sublist (List.drop_sublist_drop_left word hcut) hz
  · rw [List.drop_eq_nil_of_le (by omega : word.length ≤ cutoff)]
    rfl

/-- Replacing an equally sized segment preserves zero padding when the new
segment is itself zero beyond the global cutoff. -/
theorem replace_preserves_zero_padding (before old replacement after : List Bool) (n : ℕ)
    (hlen : old.length = replacement.length)
    (hz : allZero ((before ++ (old ++ after)).drop n) = true)
    (hnew : allZero (replacement.drop (n - before.length)) = true) :
    allZero ((before ++ (replacement ++ after)).drop n) = true := by
  simp only [List.drop_append, allZero_append, Bool.and_eq_true] at hz ⊢
  exact ⟨hz.1, hnew, by simpa only [hlen] using hz.2.2⟩

/-- A uniform array's flat address is the chunk address times the width plus
the offset within that chunk. The optional form also covers absent chunks. -/
theorem flatten_getElem?_chunk (chunks : List (List Bool)) (ell j offset : ℕ)
    (hrows : ∀ row ∈ chunks, row.length = ell) (hoffset : offset < ell) :
    chunks.flatten[j * ell + offset]? =
      (chunks[j]?).bind (fun row => row[offset]?) := by
  induction chunks generalizing j with
  | nil => simp
  | cons row rest ih =>
      have hrow : row.length = ell := hrows row (by simp)
      have hrest : ∀ x ∈ rest, x.length = ell := fun x hx => hrows x (by simp [hx])
      cases j with
      | zero =>
          simpa only [Nat.zero_mul, Nat.zero_add, List.flatten_cons,
            List.getElem?_cons_zero, Option.bind_some] using
            (List.getElem?_append_left (l₂ := rest.flatten) (by omega : offset < row.length))
      | succ j =>
          rw [List.flatten_cons, List.getElem?_append_right (by
            rw [hrow, Nat.add_mul, Nat.one_mul]
            omega : row.length ≤ (j + 1) * ell + offset)]
          have hindex : (j + 1) * ell + offset - row.length = j * ell + offset := by
            rw [hrow, Nat.add_mul]
            omega
          simpa only [hindex, List.getElem?_cons_succ] using ih j hrest

/-- Trimming the final padding never changes a genuine input-variable bit. -/
theorem take_flatten_getElem?_chunk (chunks : List (List Bool)) (ell j offset n : ℕ)
    (hrows : ∀ row ∈ chunks, row.length = ell) (hoffset : offset < ell)
    (hinput : j * ell + offset < n) :
    (chunks.flatten.take n)[j * ell + offset]? =
      (chunks[j]?).bind (fun row => row[offset]?) := by
  rw [List.getElem?_take_of_lt hinput]
  exact flatten_getElem?_chunk chunks ell j offset hrows hoffset

/-- Every emitted scope label occupies its own flat chunk when scope indices
are distinct; label order need not be sorted. -/
theorem materialize_flat_getElem? {D : ℕ} (ell width : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (j : Fin D) (label : List Bool) (offset : ℕ)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hmem : (j, label) ∈ jobs)
    (hoffset : offset < ell) :
    (materialize ell jobs chunks valid).1.flatten[j.val * ell + offset]? = label[offset]? := by
  rw [flatten_getElem?_chunk _ ell j.val offset
    (materialize_uniform ell width jobs chunks valid hrows hwidth hell) hoffset,
    materialize_lookup ell jobs chunks valid j label hcount hdistinct hmem]
  simpa only [Option.bind_some] using
    (List.getElem?_take_of_lt (l := label) hoffset)

theorem materialize_take_getElem? {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (j : Fin D) (label : List Bool) (offset : ℕ)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hmem : (j, label) ∈ jobs)
    (hoffset : offset < ell) (hinput : j.val * ell + offset < n) :
    ((materialize ell jobs chunks valid).1.flatten.take n)[j.val * ell + offset]? =
      label[offset]? := by
  rw [List.getElem?_take_of_lt hinput]
  exact materialize_flat_getElem? ell width jobs chunks valid j label offset
    hcount hrows hwidth hell hdistinct hmem hoffset

/-- The actual finalizer returns exactly `n` assignment bits whenever the
allocated uniform array contains at least `n` bits. -/
theorem materialize_take_length {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hn : n ≤ D * ell) :
    ((materialize ell jobs chunks valid).1.flatten.take n).length = n := by
  rw [List.length_take, flatten_length_uniform _ ell
    (materialize_uniform ell width jobs chunks valid hrows hwidth hell),
    materialize_length, hcount, Nat.min_eq_left hn]

theorem patchChunks_preserves_zero_padding (chunks : List (List Bool))
    (ell j n : ℕ) (replacement : List Bool)
    (hj : j < chunks.length) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hlen : replacement.length = ell)
    (hz : allZero (chunks.flatten.drop n) = true)
    (hnew : allZero (replacement.drop (n - j * ell)) = true) :
    allZero ((patchChunks j replacement chunks).flatten.drop n) = true := by
  obtain ⟨before, old, after, hsplit, hjlen⟩ := chunks_split chunks j hj
  have hbefore : ∀ row ∈ before, row.length = ell := by
    intro row hr
    exact hrows row (by rw [hsplit]; simp [hr])
  have hold : old.length = ell := hrows old (by rw [hsplit]; simp)
  have hbeforelen : before.flatten.length = j * ell := by
    rw [flatten_length_uniform before ell hbefore, hjlen]
  have hflat : chunks.flatten = before.flatten ++ (old ++ after.flatten) := by
    rw [hsplit]
    simp only [List.flatten_append, List.flatten_cons]
  have hpatched : (patchChunks j replacement chunks).flatten =
      before.flatten ++ (replacement ++ after.flatten) := by
    rw [hsplit, ← hjlen, patchChunks_append]
    simp only [List.flatten_append, List.flatten_cons]
  rw [hpatched]
  exact replace_preserves_zero_padding before.flatten old replacement after.flatten n
    (hold.trans hlen.symm) (by simpa only [← hflat] using hz)
    (by simpa only [hbeforelen] using hnew)

/-- Padding validity is preserved through the actual sequence of chunk
updates whenever every label is zero after its true remaining input width. -/
theorem materialize_preserves_zero_padding {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hz : allZero (chunks.flatten.drop n) = true)
    (hlabels : ∀ job ∈ jobs, allZero (job.2.drop (n - job.1.val * ell)) = true) :
    allZero ((materialize ell jobs chunks valid).1.flatten.drop n) = true := by
  induction jobs generalizing chunks valid with
  | nil => exact hz
  | cons job rest ih =>
      rcases job with ⟨j, label⟩
      have hlen : (label.take ell).length = ell := by
        rw [List.length_take, hwidth (j, label) (by simp), Nat.min_eq_left hell]
      have hnew : allZero ((label.take ell).drop (n - j.val * ell)) = true := by
        rw [List.drop_take]
        exact allZero_sublist (List.take_sublist _ _)
          (hlabels (j, label) (by simp))
      exact ih (patchChunks j.val (label.take ell) chunks)
        (valid && allZero (label.drop ell))
        (by rw [patchChunks_length, hcount])
        (patchChunks_uniform _ _ _ _ hlen hrows)
        (fun next hn => hwidth next (by simp [hn]))
        (patchChunks_preserves_zero_padding chunks ell j.val n (label.take ell)
          (by simpa only [hcount] using j.isLt) hrows hlen hz hnew)
        (fun next hn => hlabels next (by simp [hn]))

/-- The clause evaluator reads the corresponding low label bit at every
materialized variable address. Proofs of word lengths do not affect the read. -/
theorem materialize_wordAssignment {D n : ℕ} (ell width : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (j : Fin D) (label : List Bool) (offset : ℕ) (v : Fin n)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hmem : (j, label) ∈ jobs)
    (hoffset : offset < ell) (hv : v.val = j.val * ell + offset)
    (hlen : ((materialize ell jobs chunks valid).1.flatten.take n).length = n) :
    SubexpClauseRowProgram.wordAssignment
      ((materialize ell jobs chunks valid).1.flatten.take n) hlen v =
      label[offset]'(by have hw : label.length = width := hwidth (j, label) hmem; omega) := by
  apply Option.some.inj
  calc
    some (SubexpClauseRowProgram.wordAssignment
        ((materialize ell jobs chunks valid).1.flatten.take n) hlen v) =
        ((materialize ell jobs chunks valid).1.flatten.take n)[v.val]? := by
      symm
      exact List.getElem?_eq_getElem (by simpa only [hlen] using v.isLt)
    _ = label[offset]? := by
      rw [hv]
      exact materialize_take_getElem? ell width n jobs chunks valid j label offset
        hcount hrows hwidth hell hdistinct hmem hoffset (by simpa only [← hv] using v.isLt)
    _ = some (label[offset]'(by have hw : label.length = width := hwidth (j, label) hmem; omega)) :=
      List.getElem?_eq_getElem (by have hw : label.length = width := hwidth (j, label) hmem; omega)

/-- The actual variable read is the semantic little-endian chunk decoder.
The semantic width `b` may be smaller than the padded width `ell`. -/
theorem materialize_wordAssignment_decodeZMod {D n b p : ℕ} (ell width : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (j : Fin D) (label : List Bool) (a : ZMod p) (offset : Fin b) (v : Fin n)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hmem : (j, label) ∈ jobs)
    (hb : b ≤ ell) (hvalue : BinaryArithmetic.toNat label = a.val)
    (hv : v.val = j.val * ell + offset.val)
    (hlen : ((materialize ell jobs chunks valid).1.flatten.take n).length = n) :
    SubexpClauseRowProgram.wordAssignment
      ((materialize ell jobs chunks valid).1.flatten.take n) hlen v =
      BooleanPackingLE.decodeZMod b a offset := by
  rw [materialize_wordAssignment ell width jobs chunks valid j label offset.val v
    hcount hrows hwidth hell hdistinct hmem (offset.isLt.trans_le hb) hv hlen]
  exact BooleanPackingLE.word_getElem_eq_decodeZMod a label hvalue
    (by have hw : label.length = width := hwidth (j, label) hmem; omega) offset

/-- Every literal read by the actual clause program agrees with the local
decoded table. Coverage is a relation between the concrete job list and the
given local labels; no semantic evaluation is used as a machine instruction. -/
theorem materialize_clause_eq_cnfTable {D n p : ℕ} {b : Fin D → ℕ}
    (ell width : ℕ) (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
    (F : SAT.CNF (Fin n)) (e : {C // C ∈ F})
    (x : {j // j ∈ FactorReduction.cnfScope positions F e} → ZMod p)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (literals : List (SAT.Literal (Fin n))) (hliterals : literals.toFinset = e.val)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hsize : ∀ j, b j ≤ ell)
    (hpositions : ∀ v : Fin n, v.val = (positions v).1.val * ell + (positions v).2.val)
    (hcovered : ∀ j : {j // j ∈ FactorReduction.cnfScope positions F e},
      ∃ label, (j.val, label) ∈ jobs ∧
      BinaryArithmetic.toNat label = (x j).val)
    (hlen : ((materialize ell jobs chunks valid).1.flatten.take n).length = n) :
    literals.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment
      ((materialize ell jobs chunks valid).1.flatten.take n) hlen)) =
      FactorReduction.cnfTable positions F e
        (fun j => BooleanPackingLE.decodeZMod (b j.val) (x j)) := by
  have hread : ∀ l ∈ e.val,
      SubexpClauseRowProgram.wordAssignment
        ((materialize ell jobs chunks valid).1.flatten.take n) hlen l.variable =
      (if h : (positions l.variable).1 ∈ FactorReduction.cnfScope positions F e then
        BooleanPackingLE.decodeZMod (b (positions l.variable).1)
          (x ⟨(positions l.variable).1, h⟩) (positions l.variable).2 else false) := by
    intro l hl
    have hm : (positions l.variable).1 ∈ FactorReduction.cnfScope positions F e :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    obtain ⟨label, hjob, hvalue⟩ := hcovered ⟨(positions l.variable).1, hm⟩
    rw [dite_eq_left hm]
    exact materialize_wordAssignment_decodeZMod ell width jobs chunks valid
      (positions l.variable).1 label (x ⟨(positions l.variable).1, hm⟩)
      (positions l.variable).2 l.variable hcount hrows hwidth hell hdistinct hjob
      (hsize _) hvalue (hpositions _) hlen
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, FactorReduction.cnfTable,
    SAT.Clause.eval_eq_true, SAT.Literal.eval_eq_true]
  constructor
  · rintro ⟨l, hl, ht⟩
    have hl' : l ∈ e.val := by
      rw [← hliterals]
      exact List.mem_toFinset.mpr hl
    exact ⟨l, hl', (hread l hl').symm.trans ht⟩
  · rintro ⟨l, hl, ht⟩
    have hl' : l ∈ literals := by
      apply List.mem_toFinset.mp
      rwa [hliterals]
    exact ⟨l, hl', (hread l hl).trans ht⟩

/-- A successful final padding check enforces the shorter true width of the
last chunk. It also forces zero on any wholly padded chunk, without assuming
the caller supplied the minimal number of chunks. -/
theorem materialize_label_valid_actualWidth {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool)) (valid : Bool)
    (j : Fin D) (label : List Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup) (hmem : (j, label) ∈ jobs)
    (hvalid : (materialize ell jobs chunks valid).2 = true)
    (hpadding : allZero ((materialize ell jobs chunks valid).1.flatten.drop n) = true) :
    BinaryArithmetic.toNat label < 2 ^ min ell (n - j.val * ell) := by
  let b := min ell (n - j.val * ell)
  have hb : b ≤ label.length := by
    have hw : label.length = width := hwidth (j, label) hmem
    dsimp [b]
    omega
  have hhigh : allZero (label.drop ell) = true := by
    simp only [materialize_validity, Bool.and_eq_true, List.all_eq_true] at hvalid
    exact hvalid.2 (j, label) hmem
  have hzero : allZero (label.drop b) = true := by
    apply (allZero_iff_getElem? _).mpr
    intro offset bit hget
    have hlabel : label[b + offset]? = some bit := by
      simpa only [List.getElem?_drop] using hget
    by_cases hsmall : b + offset < ell
    · have hn : n ≤ j.val * ell + (b + offset) := by
        dsimp [b] at hsmall ⊢
        omega
      have hflat := materialize_flat_getElem? ell width jobs chunks valid j label (b + offset)
        hcount hrows hwidth hell hdistinct hmem hsmall
      exact allZero_drop_getElem? _ n _ bit hpadding hn (hflat.trans hlabel)
    · exact allZero_drop_getElem? label ell (b + offset) bit hhigh (by omega) hlabel
  have hnum := (unary_validity_iff (label.take b) (label.drop b)).mp hzero
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hb] using hnum

theorem materialize_valid_actualWidths {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hz : allZero (chunks.flatten.drop n) = true)
    (hvalues : ∀ job ∈ jobs,
      BinaryArithmetic.toNat job.2 < 2 ^ min ell (n - job.1.val * ell)) :
    (materialize ell jobs chunks true).2 = true ∧
      allZero ((materialize ell jobs chunks true).1.flatten.drop n) = true := by
  constructor
  · simp only [materialize_validity, Bool.true_and, List.all_eq_true]
    intro job hj
    exact allZero_drop_of_lt_pow job.2 _ ell (hvalues job hj) (Nat.min_le_left _ _)
  · apply materialize_preserves_zero_padding ell width n jobs chunks true
      hcount hrows hwidth hell hz
    intro job hj
    exact allZero_drop_of_lt_pow job.2 _ _ (hvalues job hj) (Nat.min_le_right _ _)

/-- The two actual validity checks together are exactly validity at each
chunk's true input width, assuming the initial array has zero padding. -/
theorem materialize_validity_iff_actualWidths {D : ℕ} (ell width n : ℕ)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup)
    (hz : allZero (chunks.flatten.drop n) = true) :
    ((materialize ell jobs chunks true).2 = true ∧
      allZero ((materialize ell jobs chunks true).1.flatten.drop n) = true) ↔
      ∀ job ∈ jobs, BinaryArithmetic.toNat job.2 < 2 ^ min ell (n - job.1.val * ell) := by
  constructor
  · rintro ⟨hv, hp⟩ ⟨j, label⟩ hj
    exact materialize_label_valid_actualWidth ell width n jobs chunks true j label
      hcount hrows hwidth hell hdistinct hj hv hp
  · exact materialize_valid_actualWidths ell width n jobs chunks hcount hrows hwidth hell hz

end SubexponentialSAT.SubexpMaterializedBits

end OAI.Algorithms
