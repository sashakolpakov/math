import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketRowBounds

namespace OAI.Algorithms

/-!
# Polynomial cost and output size of the actual factor-packet stage

The size is the sum of the original encoded input streams and scalar words.
Generated groups, rows, packets, and runtime budgets are all bounded below;
none is included in the input size or supplied as a cost assumption.
-/

namespace SubexponentialSAT.SubexpFactorPacketBounds

open SubexpFactorPacketProgram
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes cacheBytes)

def inputSize (i : Inputs) : ℕ :=
  SubexpFactorPrefixProgram.inputBytes i.origins i.columns i.scopes +
    (Encoding.encodeList id i.tables).length + (cacheBytes i.cache).length +
    i.modulus.length + i.zero.length + i.one.length + 1

theorem inputSize_pos (i : Inputs) : 1 ≤ inputSize i := by unfold inputSize; omega

private theorem input_components (i : Inputs) :
    SubexpFactorPrefixProgram.inputBytes i.origins i.columns i.scopes + 1 ≤ inputSize i ∧
    (Encoding.encodeList (Encoding.encodeList id) i.origins).length ≤ inputSize i ∧
    (Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) i.columns).length ≤ inputSize i ∧
    (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes i.scopes).length ≤ inputSize i ∧
    (Encoding.encodeList id i.tables).length ≤ inputSize i ∧
    (cacheBytes i.cache).length ≤ inputSize i ∧
    i.modulus.length ≤ inputSize i ∧ i.zero.length ≤ inputSize i ∧ i.one.length ≤ inputSize i := by
  unfold inputSize SubexpFactorPrefixProgram.inputBytes
  omega

private theorem member_length_le_flatten {α : Type*} (xss : List (List α)) (xs : List α)
    (h : xs ∈ xss) : xs.length ≤ xss.flatten.length := by
  induction xss with
  | nil => simp at h
  | cons ys yss ih =>
    simp only [List.mem_cons] at h
    simp only [List.flatten_cons, List.length_append]
    rcases h with rfl | h
    · omega
    · have ht := ih h
      omega

theorem groups_bounds (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length) :
    (groups i).length ≤ inputSize i ∧
      ∀ ps ∈ groups i, PrefixBound (inputSize i) ps := by
  obtain ⟨_, hori, hcol, hscope, _⟩ := input_components i
  have hl := SubexpFactorPrefixProgram.grouped_lengths i.scopes i.origins i.columns heq hsize
  have hflat := SubexpFactorPrefixProgram.grouped_flatten i.scopes i.origins i.columns heq hsize
  change (groups i).flatten = _ at hflat
  have hlen : (groups i).length = i.scopes.length := by
    simpa only [groups, List.length_map] using congrArg List.length hl
  have hflatten : (groups i).flatten.length ≤ inputSize i := by
    rw [hflat, SubexpFactorPrefixProgram.zipPrefixes_length i.origins i.columns heq]
    exact (length_le_encoded (Encoding.encodeList id) i.origins).trans hori
  have ho : (Encoding.encodeList originBytes (groups i).flatten).length ≤ inputSize i := by
    rw [hflat]
    change (SubexpFactorPrefixProgram.originStream _).length ≤ _
    rw [SubexpFactorPrefixProgram.originStream_zip i.origins i.columns heq]
    exact hori
  have ht : (Encoding.encodeList taylorBytes (groups i).flatten).length ≤ inputSize i := by
    rw [hflat]
    change (SubexpFactorPrefixProgram.taylorStream _).length ≤ _
    rw [SubexpFactorPrefixProgram.taylorStream_zip i.origins i.columns heq]
    exact hcol
  refine ⟨?_, ?_⟩
  · rw [hlen]
    exact (length_le_encoded SubexpFactorPrefixProgram.scopeBytes i.scopes).trans hscope
  · intro ps hps
    refine ⟨(member_length_le_flatten (groups i) ps hps).trans hflatten, ?_⟩
    intro p hp
    have hmem : p ∈ (groups i).flatten := List.mem_flatten.mpr ⟨ps, hps, hp⟩
    exact ⟨(member_length_le_encoded originBytes _ p hmem).trans ho,
      (member_length_le_encoded taylorBytes _ p hmem).trans ht⟩

theorem factorInputs_bounds (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length) :
    (factorInputs i).length ≤ inputSize i ∧
    ∀ x ∈ factorInputs i, PrefixBound (inputSize i) x.prefixes ∧ x.answers.length ≤ inputSize i := by
  have hg := groups_bounds i heq hsize
  have ht := (input_components i).2.2.2.2.1
  refine ⟨?_, ?_⟩
  · have hl := (length_le_encoded id i.tables).trans ht
    simp only [factorInputs, List.length_map, List.length_zip]
    exact (Nat.min_le_right _ _).trans hl
  · intro x hx
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hx
    have hm := List.of_mem_zip hpair
    exact ⟨hg.2 _ hm.1, (member_length_le_encoded id i.tables pair.2 hm.2).trans ht⟩

theorem groups_bytes_le (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length) :
    (masters i).groups.length ≤ 100 * inputSize i ^ 3 := by
  have hB := inputSize_pos i
  have hg := groups_bounds i heq hsize
  have h := encoded_le SubexpFactorPrefixProgram.groupBytes (groups i)
    (34 * inputSize i ^ 2) (fun ps hp => groupBytes_le hB ps (hg.2 ps hp))
  have hh := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hg.1) 1)
  change (masters i).groups.length ≤ _ at hh
  nlinarith only [hh, hB]

theorem packetStream_le {B : ℕ} (hB : 1 ≤ B)
    (m : SubexpFactorPacketControl.Masters) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (hm : m.modulus.length ≤ B)
    (hz : m.zero.length ≤ B) (ho : m.one.length ≤ B)
    (hpos : 0 < BinaryArithmetic.toNat m.modulus)
    (hcache : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (inputs : List SubexpFactorPacketLocal.Input) (hlen : inputs.length ≤ B)
    (hinput : ∀ i ∈ inputs, PrefixBound B i.prefixes ∧ i.answers.length ≤ B) :
    (SubexpFactorPacketExecution.packetStream m cache inputs).length ≤ 300 * B^4 := by
  have h := encoded_le (SubexpFactorPacketLocal.factorBytes m cache) inputs (100 * B^3) (by
    intro i hi
    exact localFactorBytes_le hB m cache hc hm hz ho hpos hcache i
      (hinput i hi).1 (hinput i hi).2)
  have hh := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) 1)
  change (SubexpFactorPacketExecution.packetStream m cache inputs).length ≤ _ at hh
  have h14 : B ≤ B^4 := Nat.le_self_pow (by decide) B
  nlinarith only [hh, hB, h14]

theorem executionRuntime_le {B : ℕ} (hB : 1 ≤ B)
    (m : SubexpFactorPacketControl.Masters) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (hm : m.modulus.length ≤ B)
    (hz : m.zero.length ≤ B) (ho : m.one.length ≤ B)
    (hgroups : m.groups.length ≤ 100 * B^3) (htables : m.tables.length ≤ B)
    (hpos : 0 < BinaryArithmetic.toNat m.modulus)
    (hcache : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (inputs : List SubexpFactorPacketLocal.Input) (hlen : inputs.length ≤ B)
    (hinput : ∀ i ∈ inputs, PrefixBound B i.prefixes ∧ i.answers.length ≤ B) :
    SubexpFactorPacketExecution.runtimeBound m cache inputs ≤ 30000 * B^5 := by
  have hlocal : ∀ i ∈ inputs, SubexpFactorPacketLocal.localBudget m cache i ≤ 20000 * B^4 := by
    intro i hi
    exact localBudget_le hB m cache hc hm hz ho hpos hcache i (hinput i hi).1 (hinput i hi).2
  have hscan : SubexpFactorPacketExecution.scanBudget m cache inputs ≤
      inputs.length * (20000 * B^4 + 3) + 3 := by
    induction inputs with
    | nil => simp [SubexpFactorPacketExecution.scanBudget]
    | cons i inputs ih =>
      have hh := hlocal i (by simp)
      have ht := ih (by simp only [List.length_cons] at hlen; omega)
        (fun x hx => hinput x (by simp [hx])) (fun x hx => hlocal x (by simp [hx]))
      simp only [SubexpFactorPacketExecution.scanBudget, List.length_cons]
      nlinarith only [hh, ht]
  have hs := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 3)
  have hp := packetStream_le hB m cache hc hm hz ho hpos hcache inputs.reverse
    (by simpa only [List.length_reverse] using hlen)
    (fun i hi => hinput i (by simpa only [List.mem_reverse] using hi))
  have h15 : B ≤ B^5 := Nat.le_self_pow (by decide) B
  have h35 : B^3 ≤ B^5 := Nat.pow_le_pow_right hB (by decide)
  have h45 : B^4 ≤ B^5 := Nat.pow_le_pow_right hB (by decide)
  unfold SubexpFactorPacketExecution.runtimeBound
  nlinarith only [hs, hp, hgroups, htables, hB, h15, h35, h45]

/-- Only original encoded input lengths occur on the right-hand side. -/
theorem runtimeBound_le (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length) :
    SubexpFactorPacketProgram.runtimeBound i ≤ 100000 * inputSize i ^ 5 := by
  obtain ⟨hprefix, _, _, _, ht, hc, hmod, hz, ho⟩ := input_components i
  have hB := inputSize_pos i
  have hf := factorInputs_bounds i heq hsize
  have hg := groups_bytes_le i heq hsize
  have hp := (SubexpFactorPrefixProgram.budget_grouped_le_input i.origins i.columns i.scopes
    heq hsize).trans (Nat.mul_le_mul_left 500 hprefix)
  have he := executionRuntime_le hB (masters i) i.cache hc hmod hz ho hg ht hm hcache
    (factorInputs i) hf.1 hf.2
  have h15 : inputSize i ≤ inputSize i ^ 5 := Nat.le_self_pow (by decide) _
  have h35 : inputSize i ^ 3 ≤ inputSize i ^ 5 := Nat.pow_le_pow_right hB (by decide)
  unfold SubexpFactorPacketProgram.runtimeBound
  change SubexpFactorPrefixProgram.budget (i.scopes.zip (groups i)) + 1 ≤ _ at hp
  omega

theorem output_length_le (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length) :
    (SubexpFactorPacketProgram.output i).length ≤ 300 * inputSize i ^ 4 := by
  obtain ⟨_, _, _, _, _, hc, hmod, hz, ho⟩ := input_components i
  have hf := factorInputs_bounds i heq hsize
  exact packetStream_le (inputSize_pos i) (masters i) i.cache hc hmod hz ho hm hcache
    (factorInputs i) hf.1 hf.2

/-- The polynomial bound is attached to the same actual stage execution. -/
theorem program_runsIn_bounded (i : Inputs) (d : Data) (ready : Ready d i)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (htables : i.tables.length = i.scopes.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length) :
    ∃ e : Data, BitProgram.RunsIn program (100000 * inputSize i ^ 5)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 227 []) 225 (output i) := by
  obtain ⟨e, he, hs⟩ := SubexpFactorPacketProgram.program_runsIn i d ready heq hsize htables hm hcache
  exact ⟨e, he.mono (runtimeBound_le i heq hsize hm hcache), hs⟩

end SubexponentialSAT.SubexpFactorPacketBounds

end OAI.Algorithms
