import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisStructuralBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgramExecution

namespace OAI.Algorithms

/-!
# Native-input polynomial bounds for global-basis assembly

Generated descriptor bytes are bounded from the retained local-table batch
and unary counts. The final size is measured on the actual input stacks;
no descriptor-size or execution-cost certificate is supplied by the caller.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisNativeBounds

open GlobalBasisInput (Context Location)
open GlobalBasisProgram
open GlobalBasisComplementColumns (LocalData encoded colorPrefix)
open GlobalBasisStructuralBounds

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β)
    (bound : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

def totalDimension (qs : List LocalData) : ℕ := (qs.map fun q => q.N).sum

theorem totalDimension_le_encoded (qs : List LocalData) :
    totalDimension qs ≤ (encoded qs).length := by
  induction qs with
  | nil => simp [totalDimension, encoded, Encoding.encodeList]
  | cons q qs ih =>
    have hf := GlobalBasisComplementColumns.payload_fields_le q
    simp only [totalDimension, List.map_cons, List.sum_cons]
    change q.N + totalDimension qs ≤ (encoded (q :: qs)).length
    simp only [encoded, Encoding.length_encodeList_cons]
    change q.N + totalDimension qs ≤ 2 * q.payload.length + 2 + (encoded qs).length
    omega

theorem totalDimension_reverse (qs : List LocalData) :
    totalDimension qs.reverse = totalDimension qs := by
  simp only [totalDimension, List.map_reverse, List.sum_reverse]

private theorem segment_length_le (block color : ℕ) (q : LocalData) (B : ℕ)
    (hb : block ≤ B) (hc : color ≤ B) (hq : q.N + q.rank ≤ B) :
    (GlobalBasisColumns.segmentPrefix block color q.rank (q.N-q.rank)).length ≤
      q.N * (12*B+10) := by
  have h := flatMap_length_le (List.range (q.N-q.rank))
    (fun column => GlobalBasisColumns.record (GlobalBasisColumns.Descriptor.encode
      (.localColumn block color (q.rank+column)))) (12*B+10) (by
        intro column hcolumn
        rw [localColumn_record_length]
        have hcolumn' := List.mem_range.mp hcolumn
        omega)
  simp only [List.length_range] at h
  change (GlobalBasisColumns.segmentPrefix block color q.rank (q.N-q.rank)).length ≤
    (q.N-q.rank) * (12*B+10) at h
  exact h.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

theorem colorPrefix_length_le (block B : ℕ) (qs : List LocalData)
    (hb : block ≤ B) (hlen : qs.length ≤ B)
    (hq : ∀ q ∈ qs, q.N + q.rank ≤ B) :
    (colorPrefix block qs).length ≤ totalDimension qs * (12*B+10) := by
  induction qs with
  | nil => simp [colorPrefix, totalDimension]
  | cons q qs ih =>
    have htail : qs.length ≤ B := by simp only [List.length_cons] at hlen; omega
    have hi := ih htail (fun x hx => hq x (by simp [hx]))
    have hs := segment_length_le block qs.length q B hb htail (hq q (by simp))
    simp only [colorPrefix, List.length_append, totalDimension, List.map_cons, List.sum_cons]
    change (colorPrefix block qs).length +
      (GlobalBasisColumns.segmentPrefix block qs.length q.rank (q.N-q.rank)).length ≤
      (q.N + totalDimension qs) * (12*B+10)
    nlinarith only [hi, hs]

theorem leftoverPrefix_length_le (count B : ℕ) (hc : count ≤ B) :
    (GlobalBasisColumnBlocks.leftoverPrefix count).length ≤ B * (4*B+6) := by
  have h := flatMap_length_le (List.range count)
    (fun rank => GlobalBasisColumns.record (GlobalBasisColumns.Descriptor.encode
      (.leftover rank))) (4*B+6) (by
        intro rank hrank
        have hr := List.mem_range.mp hrank
        simp only [GlobalBasisColumns.record, GlobalBasisColumns.Descriptor.encode,
          GlobalBasisColumns.unary, List.length_cons, Encoding.length_frame,
          List.length_replicate]
        omega)
  simp only [List.length_range] at h
  exact h.trans (Nat.mul_le_mul_right _ hc)

/-- The total local dimension is charged once to the serialized batch,
which keeps the generated complement descriptor stream cubic. -/
theorem outputPrefix_length_le (count leftovers B : ℕ) (qs : List LocalData)
    (hB : 1 ≤ B) (hc : count ≤ B) (hl : leftovers ≤ B)
    (hbytes : (encoded qs).length ≤ B) :
    (SubexpComplementColumnBatch.outputPrefix count leftovers qs).length ≤ 32*B^3 := by
  have hdim : totalDimension qs.reverse ≤ B := by
    rw [totalDimension_reverse]
    exact (totalDimension_le_encoded qs).trans hbytes
  have hcount : qs.reverse.length ≤ B := by
    rw [List.length_reverse]
    exact (GlobalBasisComplementColumns.count_le_encoded qs).trans hbytes
  have hfields : ∀ q ∈ qs.reverse, q.N + q.rank ≤ B := by
    intro q hq
    have hp := GlobalBasisComplementColumns.member_payload_le (List.mem_reverse.mp hq)
    have hf := GlobalBasisComplementColumns.payload_fields_le q
    omega
  have hcolor : ∀ block ∈ List.range count,
      (colorPrefix block qs.reverse).length ≤ B * (12*B+10) := by
    intro block hblock
    have hb : block ≤ B := by have := List.mem_range.mp hblock; omega
    exact (colorPrefix_length_le block B qs.reverse hb hcount hfields).trans
      (Nat.mul_le_mul_right _ hdim)
  have hblocks := flatMap_length_le (List.range count)
    (fun block => colorPrefix block qs.reverse) (B*(12*B+10)) hcolor
  simp only [List.length_range] at hblocks
  have hblocks' := hblocks.trans (Nat.mul_le_mul_right _ hc)
  have hleft := leftoverPrefix_length_le leftovers B hl
  have h23 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  have h13 : B ≤ B^3 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 3 by decide)
  change (GlobalBasisColumnBlocks.leftoverPrefix leftovers ++
    (List.range count).flatMap (fun b => colorPrefix b qs.reverse)).length ≤ 32*B^3
  rw [List.length_append]
  nlinarith only [hblocks', hleft, h23, h13]

variable {p r Q Δ : ℕ} [Fact p.Prime]

def nativeSize (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ) : ℕ :=
  sourceLength + (SelectorProgram.rawRecords C.metadata).length +
    (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length +
    r + C.position.val + locs.length + count + leftovers + GlobalBasisEntry.frameWidth p + 1

/-- Lengths of the physical input words, with the local-batch source
counted before its group lookup. -/
def inputVolume (d : Data) : ℕ :=
  (d.stacks 47).length + (d.stacks 33).length + (d.stacks 37).length +
    (d.stacks 38).length + (d.stacks 32).length + (d.stacks 46).length +
    (d.stacks 48).length + (d.stacks 49).length + (d.stacks 13).length + 1

theorem innerDescriptors_size_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (g : Fin r) :
    GlobalBasisRows.encodedSize (innerColumns C count g) ≤
      33 * (nativeSize C count leftovers locs sourceLength + 1)^3 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hf := local_fields_le_batch C g
  have hkernel : count + g.val + (C.tables g).split + 1 ≤ A := by
    have hg := g.isLt
    dsimp [A, nativeSize]
    omega
  have hp := (blockPrefix_length_bound count g.val (C.tables g).split).trans
    (Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left hkernel 3))
  change (Encoding.encodeList id (GlobalBasisRows.records
    (innerDescriptors count g.val (C.tables g).split))).length ≤ 33*A^3
  rw [innerDescriptors_encode]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have hpow : 1 ≤ A^3 := by simpa using Nat.pow_le_pow_left hA 3
  omega

theorem outerDescriptors_size_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) :
    GlobalBasisRows.encodedSize (outerColumnsList C count leftovers) ≤
      33 * (nativeSize C count leftovers locs sourceLength + 1)^3 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hc : count ≤ A := by dsimp [A, nativeSize]; omega
  have hl : leftovers ≤ A := by dsimp [A, nativeSize]; omega
  have hb : (encoded C.data).length ≤ A := by
    change C.batch.length ≤ A
    dsimp [A, nativeSize]
    omega
  have hp := outputPrefix_length_le count leftovers A C.data hA hc hl hb
  change (Encoding.encodeList id (GlobalBasisRows.records
    (outerDescriptors count leftovers C.data))).length ≤ 33*A^3
  rw [outerDescriptors_encode]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have hpow : 1 ≤ A^3 := by simpa using Nat.pow_le_pow_left hA 3
  omega

private theorem volume_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (xs : List GlobalBasisColumns.Descriptor)
    (hxs : GlobalBasisRows.encodedSize xs ≤
      33 * (nativeSize C count leftovers locs sourceLength + 1)^3) :
    volume C locs xs + 1 ≤ 34 * (nativeSize C count leftovers locs sourceLength + 1)^3 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have h13 : A ≤ A^3 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 3 by decide)
  have hv : volume C locs xs + 1 ≤ A + GlobalBasisRows.encodedSize xs := by
    dsimp [volume, inputSize, A, nativeSize]
    omega
  change GlobalBasisRows.encodedSize xs ≤ 33*A^3 at hxs
  change volume C locs xs + 1 ≤ 34*A^3
  omega

theorem matrixBudget_native_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (hm : C.locations 0 locs)
    (xs : List GlobalBasisColumns.Descriptor)
    (hxs : GlobalBasisRows.encodedSize xs ≤
      33 * (nativeSize C count leftovers locs sourceLength + 1)^3) :
    matrixBudget C xs locs ≤
      2000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^18 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have h := (matrixBudget_le C locs xs hm).trans
    (Nat.mul_le_mul_left 1000000
      (Nat.pow_le_pow_left (volume_le C count leftovers locs sourceLength hbatch xs hxs) 6))
  change matrixBudget C xs locs ≤ 1000000*(34*A^3)^6 at h
  change matrixBudget C xs locs ≤ 2000000000000000*A^18
  norm_num [mul_pow, ← pow_mul] at h
  nlinarith only [h]

omit [Fact p.Prime] in
theorem matrixOutput_native_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (xs : List GlobalBasisColumns.Descriptor)
    (hxs : GlobalBasisRows.encodedSize xs ≤
      33 * (nativeSize C count leftovers locs sourceLength + 1)^3) :
    GlobalBasisMatrixOutput.cost (List.replicate xs.length true) (matrixBits C locs xs)
      (Encoding.encodeList id (GlobalBasisRows.records xs)) ≤
        6000 * (nativeSize C count leftovers locs sourceLength + 1)^5 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hn : locs.length ≤ A := by dsimp [A, nativeSize]; omega
  have hf : GlobalBasisEntry.frameWidth p ≤ A := by dsimp [A, nativeSize]; omega
  change GlobalBasisRows.encodedSize xs ≤ 33*A^3 at hxs
  have hcount := (GlobalBasisRows.length_le_encodedSize xs).trans hxs
  have hmatrix : (matrixBits C locs xs).length ≤ 33*A^5 := by
    rw [matrixBits_length]
    have h := Nat.mul_le_mul (Nat.mul_le_mul hn hcount) hf
    nlinarith only [h]
  have h := GlobalBasisMatrixOutput.cost_le_linear (List.replicate xs.length true)
    (matrixBits C locs xs) (Encoding.encodeList id (GlobalBasisRows.records xs))
  simp only [List.length_replicate] at h
  change GlobalBasisMatrixOutput.cost _ _ _ ≤
    56*(xs.length+(matrixBits C locs xs).length+GlobalBasisRows.encodedSize xs+1) at h
  have h35 : A^3 ≤ A^5 := Nat.pow_le_pow_right hA (by decide)
  have h05 : 1 ≤ A^5 := by simpa using Nat.pow_le_pow_left hA 5
  change GlobalBasisMatrixOutput.cost _ _ _ ≤ 6000*A^5
  nlinarith only [h, hcount, hxs, hmatrix, h35, h05]

theorem innerStepBudget_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (hm : C.locations 0 locs) (g : Fin r) :
    innerStepBudget C count locs g ≤
      10000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^18 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hf := local_fields_le_batch C g
  have hp := innerBudget_polynomial C.batch.length count g.val
    (C.tables g).dimension (C.tables g).split (C.tables g).bits.length
    (by omega) (by omega) (by omega)
  have hs : innerSize C.batch.length count g.val ≤ A := by
    have hg := g.isLt
    dsimp [innerSize, A, nativeSize]
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hs 3))
  have hd := innerDescriptors_size_le C count leftovers locs sourceLength hbatch g
  have hm' := matrixBudget_native_le C count leftovers locs sourceLength hbatch hm _ hd
  have ho := matrixOutput_native_le C count leftovers locs sourceLength _ hd
  have h318 : A^3 ≤ A^18 := Nat.pow_le_pow_right hA (by decide)
  have h518 : A^5 ≤ A^18 := Nat.pow_le_pow_right hA (by decide)
  change innerStepBudget C count locs g ≤ 10000000000000000*A^18
  unfold innerStepBudget
  change innerBudget _ _ _ _ _ _ + 1 ≤ 500*A^3 at hp'
  change matrixBudget _ _ _ ≤ 2000000000000000*A^18 at hm'
  change GlobalBasisMatrixOutput.cost _ _ _ ≤ 6000*A^5 at ho
  nlinarith only [hp', hm', ho, h318, h518]

theorem outerPhaseBudget_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (hm : C.locations 0 locs) :
    outerPhaseBudget C count leftovers locs ≤
      10000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^18 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hp := outerBudget_polynomial count leftovers C.data
  have hs : SubexpComplementColumnBatch.sizeParameter count leftovers C.data ≤ 2*A := by
    change count+leftovers+2*C.batch.length+1 ≤ 2*A
    dsimp [A, nativeSize]
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left 1020 (Nat.pow_le_pow_left hs 4))
  have hd := outerDescriptors_size_le C count leftovers locs sourceLength hbatch
  have hm' := matrixBudget_native_le C count leftovers locs sourceLength hbatch hm _ hd
  have ho := matrixOutput_native_le C count leftovers locs sourceLength _ hd
  have h418 : A^4 ≤ A^18 := Nat.pow_le_pow_right hA (by decide)
  have h518 : A^5 ≤ A^18 := Nat.pow_le_pow_right hA (by decide)
  change outerPhaseBudget C count leftovers locs ≤ 10000000000000000*A^18
  unfold outerPhaseBudget
  change outerBudget count leftovers C.data + 1 ≤ 1020*(2*A)^4 at hp'
  change matrixBudget _ _ _ ≤ 2000000000000000*A^18 at hm'
  change GlobalBasisMatrixOutput.cost _ _ _ ≤ 6000*A^5 at ho
  nlinarith only [hp', hm', ho, h418, h518]

theorem colorBudget_le_count (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (hm : C.locations 0 locs) (colors : ℕ) :
    colorBudget C count locs colors ≤ colors *
      (10000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^18+2)+2 := by
  induction colors with
  | zero => simp [colorBudget]
  | succ colors ih =>
    have hstep : innerCostAt C count locs colors ≤
        10000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^18 := by
      unfold innerCostAt
      split
      · exact innerStepBudget_le C count leftovers locs sourceLength hbatch hm _
      · exact Nat.zero_le _
    simp only [colorBudget]
    nlinarith only [ih, hstep]

theorem totalBudget_le (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) (sourceLength : ℕ)
    (hbatch : C.batch.length ≤ sourceLength) (hm : C.locations 0 locs) :
    totalBudget C count leftovers locs sourceLength ≤
      1000000000000000000 * (nativeSize C count leftovers locs sourceLength + 1)^20 := by
  let A := nativeSize C count leftovers locs sourceLength + 1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hr : r ≤ A := by dsimp [A, nativeSize]; omega
  have hsource : sourceLength + C.position.val + 1 ≤ A := by dsimp [A, nativeSize]; omega
  have hb : C.batch.length ≤ A := by dsimp [A, nativeSize]; omega
  have hc := colorBudget_le_count C count leftovers locs sourceLength hbatch hm r
  have ho := outerPhaseBudget_le C count leftovers locs sourceLength hbatch hm
  change colorBudget C count locs r ≤ r*(10000000000000000*A^18+2)+2 at hc
  change outerPhaseBudget C count leftovers locs ≤ 10000000000000000*A^18 at ho
  have hmul := Nat.mul_le_mul_right (10000000000000000*A^18+2) hr
  have h120 : A ≤ A^20 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 20 by decide)
  have h1820 : A^18 ≤ A^20 := Nat.pow_le_pow_right hA (by decide)
  have h1920 : A^19 ≤ A^20 := Nat.pow_le_pow_right hA (by decide)
  change totalBudget C count leftovers locs sourceLength ≤ 1000000000000000000*A^20
  unfold totalBudget
  nlinarith only [hc, ho, hmul, hr, hsource, hb, hA, h120, h1820, h1920]

theorem Inputs.batch_le {C : Context p r Q Δ} {count leftovers : ℕ}
    {locs : List (Location r Q Δ)} {before : List (List Bool)} {tail : List Bool} {d : Data}
    (H : Inputs C count leftovers locs before tail d) : C.batch.length ≤ (d.stacks 47).length := by
  rw [H.group]
  simp only [List.length_append, GlobalBasisRecordLookup.record, List.length_cons,
    Encoding.length_frame]
  omega

theorem Inputs.nativeSize_eq {C : Context p r Q Δ} {count leftovers : ℕ}
    {locs : List (Location r Q Δ)} {before : List (List Bool)} {tail : List Bool} {d : Data}
    (H : Inputs C count leftovers locs before tail d) :
    nativeSize C count leftovers locs (d.stacks 47).length = inputVolume d := by
  simp only [nativeSize, inputVolume, H.width, H.position, H.metadata, H.universal,
    H.colors, H.dimension, H.blocks, H.leftovers, List.length_replicate]

/-- The completed numeric bound uses the original physical input words.
Only successful row metadata and the actual input encoding are required. -/
theorem totalBudget_input_le {C : Context p r Q Δ} {count leftovers : ℕ}
    {locs : List (Location r Q Δ)} {before : List (List Bool)} {tail : List Bool} {d : Data}
    (H : Inputs C count leftovers locs before tail d) (hm : C.locations 0 locs) :
    totalBudget C count leftovers locs (d.stacks 47).length ≤
      1000000000000000000 * (inputVolume d + 1)^20 := by
  simpa only [Inputs.nativeSize_eq H] using
    totalBudget_le C count leftovers locs (d.stacks 47).length (Inputs.batch_le H) hm

end SubexponentialSAT.Subexp.GlobalBasisNativeBounds

end OAI.Algorithms
