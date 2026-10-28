import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgramSupport
import OAI.Algorithms.SubexponentialSAT.SubexpComplementColumnBatchBounds

namespace OAI.Algorithms

/-!
# Native column preparation

The inner and outer native commands build their descriptor streams from
the physical local-search records and unary packing parameters. Their only
net stack change is the descriptor output on 35. Shared inputs, scalar
constants, and the final bundle accumulator remain framed.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls

def InnerClean (d : Data) : Prop :=
  ∀ i : Fin 64, i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    16, 17, 18, 19, 20, 21, 22, 31, 35] → d.stacks i = []

def OuterClean (d : Data) : Prop :=
  ∀ i : Fin 64, i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 31, 35] → d.stacks i = []

def innerBudget (bytes count color N split tableBytes : ℕ) : ℕ :=
  60 * (bytes + color + 1) + (7 * count + 5) + (7 * color + 5) +
    (7 * split + 5) + 2 + 220 * (count + color + split + 1)^3 +
    (6 * ((GlobalBasisColumnBlocks.blockPrefix count color split).length + 1) + 6) +
    (2 * color + 3 + (2 * split + 3) + (2 * N + 3) + (2 * split + 3) +
      (2 * tableBytes + 3) + (2 * (N - split) + 3))

def outerBudget (count leftovers : ℕ) (qs : List GlobalBasisComplementColumns.LocalData) : ℕ :=
  7 * count + 7 + (SubexpComplementColumnBatch.cost count leftovers qs + 1)

def innerDescriptors (count color dimension : ℕ) : List GlobalBasisColumns.Descriptor :=
  (List.range count).flatMap fun block =>
    (List.range dimension).map (GlobalBasisColumns.Descriptor.localColumn block color)

def outerDescriptors (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) : List GlobalBasisColumns.Descriptor :=
  (List.range leftovers).map GlobalBasisColumns.Descriptor.leftover ++
    (List.range count).flatMap fun block => qs.zipIdx.flatMap fun entry =>
      (List.range (entry.1.N - entry.1.rank)).map fun column =>
        GlobalBasisColumns.Descriptor.localColumn block entry.2 (entry.1.rank + column)

private theorem descriptors_encode (xs : List GlobalBasisColumns.Descriptor) :
    Encoding.encodeList id (GlobalBasisRows.records xs) =
      xs.flatMap (fun x => GlobalBasisColumns.record x.encode) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [GlobalBasisRows.records, List.map_cons, Encoding.encodeList, id_eq,
      List.flatMap_cons, GlobalBasisColumns.record, List.cons_append, List.append_assoc] using congrArg
      (fun tail => true :: (Encoding.frame x.encode ++ tail)) ih

theorem innerDescriptors_encode (count color dimension : ℕ) :
    Encoding.encodeList id (GlobalBasisRows.records (innerDescriptors count color dimension)) =
      GlobalBasisColumnBlocks.blockPrefix count color dimension ++ [false] := by
  rw [descriptors_encode]
  simp [innerDescriptors, GlobalBasisColumnBlocks.blockPrefix,
    GlobalBasisColumns.segmentPrefix, List.flatMap_assoc, List.flatMap_map]

theorem outerDescriptors_encode (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) :
    Encoding.encodeList id (GlobalBasisRows.records (outerDescriptors count leftovers qs)) =
      SubexpComplementColumnBatch.outputPrefix count leftovers qs ++ [false] := by
  rw [descriptors_encode, SubexpComplementColumnBatch.outputPrefix_order]
  simp [outerDescriptors, GlobalBasisColumns.segmentPrefix, List.flatMap_assoc,
    List.flatMap_map, List.flatMap_append, List.append_assoc]

/-- The split is read by the actual record lookup and parser. No descriptor
plan or semantic selection function is passed to the native command. -/
theorem prepareInner_eval (before : List (List Bool)) (N split count : ℕ)
    (table tail : List Bool) (d : Data)
    (h40 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split table) ++ tail)
    (h55 : d.stacks 55 = GlobalBasisRecordLookup.unary before.length)
    (h48 : d.stacks 48 = List.replicate count true) (hc : InnerClean d) :
    ∃ n e, n ≤ innerBudget (d.stacks 40).length count before.length N split table.length ∧
      Eval prepareInner n d e ∧ e.stacks = Function.update d.stacks 35
        (GlobalBasisColumnBlocks.blockPrefix count before.length split ++ [false]) := by
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  have h5 := hc 5 (by decide)
  have h6 := hc 6 (by decide)
  have h7 := hc 7 (by decide)
  have h8 := hc 8 (by decide)
  have h9 := hc 9 (by decide)
  have h10 := hc 10 (by decide)
  have h16 := hc 16 (by decide)
  have h17 := hc 17 (by decide)
  have h18 := hc 18 (by decide)
  have h19 := hc 19 (by decide)
  have h31 := hc 31 (by decide)
  have h35 := hc 35 (by decide)
  have hclean : GlobalBasisDataLookup.Clean (projectState regs8 splitPorts d) := by
    intro i hi hj
    change d.stacks (splitPorts i) = []
    apply hc
    fin_cases i <;> norm_num [splitPorts, Fin.coe_ofNat_eq_mod] at *
  obtain ⟨n₀, a, hn₀, ha, hsa⟩ := getSplit_eval before N split table tail d h40 h55 hclean
  let b := copied 48 0 a
  let c := copied 55 1 b
  let f := copied 17 10 c
  let g := TupleProgram.pushedState 3 0 false f
  have hb := copy_eval 48 0 a (by decide) (by decide) (by decide)
    (by simp [hsa, h31])
  have hc' := copy_eval 55 1 b (by decide) (by decide) (by decide)
    (by simp [b, copied, StackRoutines.copyStacks, hsa, h31])
  have hf := copy_eval 17 10 c (by decide) (by decide) (by decide)
    (by simp [c, b, copied, StackRoutines.copyStacks, hsa, h31])
  have hg := push_eval 3 false f
  have hgs : g.stacks = Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update d.stacks 16 (List.replicate N true))
          17 (List.replicate split true)) 18 table) 19 (List.replicate (N-split) true))
        0 (List.replicate count true)) 1 (List.replicate before.length true))
      10 (List.replicate split true)) 3 [false] := by
    simp [g, f, c, b, copied, StackRoutines.copyStacks,
      hsa, h0, h1, h3, h10, h48, h55, GlobalBasisRecordLookup.unary]
  obtain ⟨n₁, k, hn₁, hk, hsk⟩ := kernelColumns_eval count before.length split g
    (by simp [hgs]) (by simp [hgs]) (by simp [hgs, h2])
    (by simp [hgs, h4]) (by simp [hgs, h5]) (by simp [hgs, h6])
    (by simp [hgs, h7]) (by simp [hgs, h8]) (by simp [hgs, h9]) (by simp [hgs])
  obtain ⟨m, hm, hsm⟩ := move_eval 3 35 k (by decide) (by decide) (by decide)
    (by simp [hsk, hgs, h31])
  obtain ⟨n₂, e, hn₂, he, hse⟩ := clearList_eval [1, 10, 16, 17, 18, 19] m
  have ht := ha.seq (hb.seq (hc'.seq (hf.seq (hg.seq (hk.seq (hm.seq
    (he.seq (.base (.skip e)))))))))
  have hsrc48 : a.stacks 48 = List.replicate count true := by simp [hsa, h48]
  have hsrc55 : b.stacks 55 = List.replicate before.length true := by
    simp [b, copied, StackRoutines.copyStacks, hsa, h55, GlobalBasisRecordLookup.unary]
  have hsrc17 : c.stacks 17 = List.replicate split true := by
    simp [c, b, copied, StackRoutines.copyStacks, hsa]
  have hk3 : k.stacks 3 = GlobalBasisColumnBlocks.blockPrefix count before.length split ++ [false] := by
    simp [hsk, hgs]
  have hclear : clearBudget [1, 10, 16, 17, 18, 19] m.stacks =
      2 * before.length + 3 + (2 * split + 3) + (2 * N + 3) + (2 * split + 3) +
        (2 * table.length + 3) + (2 * (N - split) + 3) := by
    simp [clearBudget, hsm, hsk, hgs]
    omega
  rw [hsrc48, hsrc55, hsrc17, hk3] at ht
  simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil,
    Nat.add_zero] at ht
  refine ⟨_, e, ?_, by simpa only [prepareInner, sequence, List.foldr] using ht, ?_⟩
  · simp only [innerBudget]
    rw [h55] at hn₀
    simp only [GlobalBasisRecordLookup.unary, List.length_replicate] at hn₀
    rw [hclear] at hn₂
    omega
  · rw [hse]
    funext i
    fin_cases i <;> simp [hsm, hsk, hgs, h0, h1, h3, h10, h16, h17, h18, h19, h35]

/-- The outer command reverses and expands the physical forward batch
inside the called generator, then restores every working stack. -/
theorem prepareOuter_eval (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) (d : Data)
    (h40 : d.stacks 40 = GlobalBasisComplementColumns.encoded qs)
    (h38 : d.stacks 38 = List.replicate qs.length true)
    (h48 : d.stacks 48 = List.replicate count true)
    (h49 : d.stacks 49 = List.replicate leftovers true) (hc : OuterClean d) :
    ∃ n e, n ≤ outerBudget count leftovers qs ∧ Eval prepareOuter n d e ∧
      e.stacks = Function.update d.stacks 35
        (SubexpComplementColumnBatch.outputPrefix count leftovers qs ++ [false]) := by
  have h0 := hc 0 (by decide)
  have h31 := hc 31 (by decide)
  have h35 := hc 35 (by decide)
  let a := copied 48 0 d
  let b := TupleProgram.pushedState 35 0 false a
  have ha := copy_eval 48 0 d (by decide) (by decide) (by decide) h31
  have hb := push_eval 35 false a
  have hbs : b.stacks = Function.update
      (Function.update d.stacks 0 (List.replicate count true)) 35 [false] := by
    simp [b, a, copied, StackRoutines.copyStacks, h48, h0, h35]
  have hready : SubexpComplementColumnBatch.Ready (projectState regs8 outerPorts b) := by
    intro i hi0 hi3 hi22 hi23 hi24 hi25
    fin_cases i <;> simp_all [projectState, outerPorts]
    all_goals
      apply hc
      decide
  obtain ⟨n, e, hn, he, hse⟩ := outerColumns_eval count leftovers qs b
    (by simp [hbs]) (by simp [hbs, h40]) (by simp [hbs, h38]) (by simp [hbs, h49])
    (by simp [hbs, hc 25 (by decide)]) hready
  have ht := ha.seq (hb.seq (he.seq (.base (.skip e))))
  rw [h48] at ht
  simp only [List.length_replicate, Nat.add_zero] at ht
  refine ⟨_, e, ?_, by simpa only [prepareOuter, sequence, List.foldr] using ht, ?_⟩
  · unfold outerBudget
    omega
  · rw [hse, hbs]
    funext i
    by_cases h : i = 35
    · subst i; simp
    · by_cases h' : i = 0
      · subst i; simp [h0]
      · simp [Function.update_of_ne h, Function.update_of_ne h']

private theorem flatMap_length_le {A B : Type*} (xs : List A) (f : A → List B)
    (bound : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    omega

theorem localColumn_record_length (block color column : ℕ) :
    (GlobalBasisColumns.record (GlobalBasisColumns.Descriptor.encode
      (.localColumn block color column))).length = 4 * (block + color + column) + 10 := by
  simp [GlobalBasisColumns.record, GlobalBasisColumns.Descriptor.encode,
    GlobalBasisColumns.localPayload, GlobalBasisColumns.unary]
  omega

/-- The descriptor output itself has a cubic byte bound, including the
unary indices written by the concrete emitters. -/
theorem blockPrefix_length_bound (count color dimension : ℕ) :
    (GlobalBasisColumnBlocks.blockPrefix count color dimension).length ≤
      14 * (count + color + dimension + 1)^3 := by
  let S := count + color + dimension + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hc : count ≤ S := by dsimp [S]; omega
  have hd : dimension ≤ S := by dsimp [S]; omega
  have hsegment : ∀ block ∈ List.range count,
      (GlobalBasisColumns.segmentPrefix block color 0 dimension).length ≤ dimension * (14 * S) := by
    intro block hb
    have hb' := List.mem_range.mp hb
    have h := flatMap_length_le (List.range dimension)
      (fun column => GlobalBasisColumns.record (GlobalBasisColumns.Descriptor.encode
        (.localColumn block color (0 + column)))) (14 * S) (by
          intro column hcol
          rw [localColumn_record_length]
          have hcol' := List.mem_range.mp hcol
          dsimp [S]
          omega)
    simpa only [GlobalBasisColumns.segmentPrefix, List.length_range] using h
  have h := flatMap_length_le (List.range count)
    (fun block => GlobalBasisColumns.segmentPrefix block color 0 dimension)
    (dimension * (14 * S)) hsegment
  simp only [List.length_range] at h
  have hp := Nat.mul_le_mul hc hd
  have hp' := Nat.mul_le_mul_right (14 * S) hp
  change (GlobalBasisColumnBlocks.blockPrefix count color dimension).length ≤ 14 * S^3
  change (GlobalBasisColumnBlocks.blockPrefix count color dimension).length ≤
    count * (dimension * (14 * S)) at h
  nlinarith

def innerSize (bytes count color : ℕ) : ℕ := bytes + count + color + 1

theorem innerBudget_polynomial (bytes count color N split tableBytes : ℕ)
    (hN : N ≤ bytes) (hsplit : split ≤ bytes) (htable : tableBytes ≤ bytes) :
    innerBudget bytes count color N split tableBytes + 1 ≤ 500 * (innerSize bytes count color)^3 := by
  let S := innerSize bytes count color
  have hS : 1 ≤ S := by dsimp [S, innerSize]; omega
  have hbytes : bytes ≤ S := by dsimp [S, innerSize]; omega
  have hc : count ≤ S := by dsimp [S, innerSize]; omega
  have hcolor : color ≤ S := by dsimp [S, innerSize]; omega
  have hkernel : count + color + split + 1 ≤ S := by dsimp [S, innerSize]; omega
  have hparse : bytes + color + 1 ≤ S := by dsimp [S, innerSize]; omega
  have hS3 : S ≤ S^3 := by
    have hS2 : S ≤ S^2 := by nlinarith
    exact hS2.trans (Nat.pow_le_pow_right hS (by decide : 2 ≤ 3))
  have hpow := Nat.pow_le_pow_left hkernel 3
  have hprefix := (blockPrefix_length_bound count color split).trans
    (Nat.mul_le_mul_left 14 hpow)
  change innerBudget bytes count color N split tableBytes + 1 ≤ 500 * S^3
  unfold innerBudget
  nlinarith [Nat.sub_le N split]

theorem outerBudget_polynomial (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) :
    outerBudget count leftovers qs + 1 ≤
      1020 * (SubexpComplementColumnBatch.sizeParameter count leftovers qs)^4 := by
  let S := SubexpComplementColumnBatch.sizeParameter count leftovers qs
  have hS : 1 ≤ S := by dsimp [S, SubexpComplementColumnBatch.sizeParameter]; omega
  have hc : count ≤ S := by dsimp [S, SubexpComplementColumnBatch.sizeParameter]; omega
  have hS4 : S ≤ S^4 := by
    have hS2 : S ≤ S^2 := by nlinarith
    exact hS2.trans (Nat.pow_le_pow_right hS (by decide : 2 ≤ 4))
  have h := SubexpComplementColumnBatch.cost_polynomial count leftovers qs
  change SubexpComplementColumnBatch.cost count leftovers qs + 1 ≤ 1000 * S^4 at h
  change outerBudget count leftovers qs + 1 ≤ 1020 * S^4
  unfold outerBudget
  nlinarith

/-- The local fields are bounded by their actual encoded input record.
Thus the native inner command has a cubic bound in input bytes and unary
packing indices, with no semantic or cost certificate supplied. -/
theorem prepareInner_eval_polynomial (before : List (List Bool)) (N split count : ℕ)
    (table tail : List Bool) (d : Data)
    (h40 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split table) ++ tail)
    (h55 : d.stacks 55 = GlobalBasisRecordLookup.unary before.length)
    (h48 : d.stacks 48 = List.replicate count true) (hc : InnerClean d) :
    ∃ n e, n + 1 ≤ 500 * (innerSize (d.stacks 40).length count before.length)^3 ∧
      Eval prepareInner n d e ∧ e.stacks = Function.update d.stacks 35
        (GlobalBasisColumnBlocks.blockPrefix count before.length split ++ [false]) := by
  obtain ⟨n, e, hn, he, hs⟩ := prepareInner_eval before N split count table tail d h40 h55 h48 hc
  have hl := congrArg List.length h40
  simp only [List.length_append, GlobalBasisRecordLookup.record, List.length_cons,
    Encoding.length_frame, SubexpLocalBatchParse.payload, SubexpLocalBatchParse.unary,
    List.length_replicate] at hl
  have hb := innerBudget_polynomial (d.stacks 40).length count before.length N split table.length
    (by omega) (by omega) (by omega)
  exact ⟨n, e, by omega, he, hs⟩

theorem prepareOuter_eval_polynomial (count leftovers : ℕ)
    (qs : List GlobalBasisComplementColumns.LocalData) (d : Data)
    (h40 : d.stacks 40 = GlobalBasisComplementColumns.encoded qs)
    (h38 : d.stacks 38 = List.replicate qs.length true)
    (h48 : d.stacks 48 = List.replicate count true)
    (h49 : d.stacks 49 = List.replicate leftovers true) (hc : OuterClean d) :
    ∃ n e, n + 1 ≤ 1020 * (SubexpComplementColumnBatch.sizeParameter count leftovers qs)^4 ∧
      Eval prepareOuter n d e ∧ e.stacks = Function.update d.stacks 35
        (SubexpComplementColumnBatch.outputPrefix count leftovers qs ++ [false]) := by
  obtain ⟨n, e, hn, he, hs⟩ := prepareOuter_eval count leftovers qs d h40 h38 h48 h49 hc
  have hb := outerBudget_polynomial count leftovers qs
  exact ⟨n, e, by omega, he, hs⟩

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
