import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryArithmetic

/-! Fixed polynomial bounds for the actual retained ring words. The modulus
is charged by its binary length. Arbitrary preserved caller words enter only
through a separate maximum; these are boundary bounds, not prefix bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingRetainedSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram

/-- The persistent words identified by the actual ring producer. -/
def ringPorts : Finset (Fin 640) :=
  {191, 194, 201, 202, 203, 204, 207, 209, 211, 212, 243, 253, 256, 280, 281, 300}

/-- The same ring words together with the actual interpolation and denominator outputs. -/
def arithmeticPorts : Finset (Fin 768) :=
  ringPorts.image LeafRingSetupProgram.wideStacks ∪ {713, 714, 715, 716, 717, 728}

/-- The four equal full-coefficient aliases are retained physical words too. -/
def allArithmeticPorts : Finset (Fin 768) :=
  arithmeticPorts ∪ {190, 249, 250, 251}

@[simp] theorem allArithmeticPorts_card : allArithmeticPorts.card = 26 := by decide

@[simp] theorem ringPorts_card : ringPorts.card = 16 := by decide

@[simp] theorem arithmeticPorts_card : arithmeticPorts.card = 22 := by decide

theorem ringPorts_lt (i : Fin 640) (hi : i ∈ ringPorts) : i.val < 340 := by
  simp only [ringPorts, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section Produced

variable {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {out : LeafRingSetupProgram.Data}

/-- This cap uses actual scalar values only for unary dimensions; it never
bounds the numerical value of the binary modulus or a count. -/
theorem produced_word_le (hp : LeafRingSetupProgram.Produced m hd M cache half out)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (i : Fin 640) (hi : i ∈ ringPorts) :
    (out.stacks i).length ≤ 7 * (S + 1)^4 := by
  obtain ⟨hmod, hwidth, hzero, hhalf⟩ := RingResources.produced_scalar_lengths hp
  obtain ⟨htable, hone, hminus, hfullzero, hidem⟩ := RingResources.produced_array_lengths hp
  obtain ⟨hnword, hdword, htword, hJword, hfieldword⟩ :=
    RingResources.produced_unary_lengths hp
  obtain ⟨hnodes, hframed⟩ := RingResources.produced_node_lengths hp
  have hs : S ≤ (S + 1)^4 :=
    (Nat.le_succ S).trans (Nat.le_self_pow (by decide) (S + 1))
  have hsmall : S ≤ 7 * (S + 1)^4 := by omega
  have hpos : 1 ≤ (S + 1)^4 := Nat.one_le_pow 4 (S + 1) (by omega)
  have hp2 : (S + 1)^2 ≤ (S + 1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp3 : (S + 1)^3 ≤ (S + 1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have htwo : 2 * m.val 34 * m.val 33 ≤ 7 * (S + 1)^4 := by
    calc
      _ ≤ 2 * (S + 1) * (S + 1) := by gcongr <;> omega
      _ = 2 * (S + 1)^2 := by ring
      _ ≤ 7 * (S + 1)^4 := by omega
  have hthree : 2 * m.val 21 * m.val 34 * m.val 33 ≤ 7 * (S + 1)^4 := by
    calc
      _ ≤ 2 * (S + 1) * (S + 1) * (S + 1) := by gcongr <;> omega
      _ = 2 * (S + 1)^3 := by ring
      _ ≤ 7 * (S + 1)^4 := by omega
  have hfour : 2 * (m.val 34)^3 * m.val 33 ≤ 7 * (S + 1)^4 := by
    calc
      _ ≤ 2 * (S + 1)^3 * (S + 1) := by gcongr <;> omega
      _ = 2 * (S + 1)^4 := by ring
      _ ≤ 7 * (S + 1)^4 := by omega
  have hi2 : 6 * (m.val 33)^2 ≤ 7 * (S + 1)^4 := by
    calc
      _ ≤ 6 * (S + 1)^2 := by gcongr; omega
      _ ≤ 7 * (S + 1)^4 := by omega
  have hfr : 1 + (4 * m.val 34 * m.val 33 + 2) * m.val 21 ≤
      7 * (S + 1)^4 := by
    have hm : 4 * m.val 34 * m.val 33 * m.val 21 ≤ 4 * (S + 1)^4 := by
      calc
        _ ≤ 4 * (S + 1) * (S + 1) * (S + 1) := by gcongr <;> omega
        _ = 4 * (S + 1)^3 := by ring
        _ ≤ 4 * (S + 1)^4 := Nat.mul_le_mul_left 4 hp3
    have hq := hQ.trans hs
    nlinarith only [hm, hq, hpos]
  have hscalar : 2 * m.val 33 + 1 ≤ 7 * (S + 1)^4 := by omega
  simp only [ringPorts, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hnword.le.trans (hn.trans hsmall)
  · exact hmod.trans hscalar
  · exact htable.le.trans hfour
  · exact hwidth.le.trans (by omega)
  · exact hzero.le.trans (by omega)
  · exact hdword.le.trans (hdim.trans hsmall)
  · exact hone.le.trans htwo
  · exact hfieldword.le.trans (hfield.trans hsmall)
  · exact hminus.le.trans htwo
  · exact htword.le.trans (ht.trans hsmall)
  · exact hJword.le.trans (hJ.trans hsmall)
  · exact hhalf.le.trans (by omega)
  · exact hnodes.le.trans hthree
  · exact hfullzero.le.trans htwo
  · exact hidem.le.trans hi2
  · exact hframed.trans hfr

/-- Sum of all sixteen identified retained words, including both node encodings. -/
theorem produced_bits_le (hp : LeafRingSetupProgram.Produced m hd M cache half out)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S) :
    selectedStackBits ringPorts out.stacks ≤ 112 * (S + 1)^4 := by
  have h := ringPorts.sum_le_card_nsmul (fun i => (out.stacks i).length)
    (7 * (S + 1)^4) (produced_word_le hp S hn ht hdim hQ hJ hfield)
  simpa [selectedStackBits, nsmul_eq_mul, ← Nat.mul_assoc] using h

/-- The producer retains these four additional copies of its full constants. -/
theorem produced_alias_le (hp : LeafRingSetupProgram.Produced m hd M cache half out)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (i : Fin 640) (hi : i ∈ ({190, 249, 250, 251} : Finset (Fin 640))) :
    (out.stacks i).length ≤ 7 * (S + 1)^4 := by
  have hzero := produced_word_le hp S hn ht hdim hQ hJ hfield 280 (by decide)
  have hone := produced_word_le hp S hn ht hdim hQ hJ hfield 207 (by decide)
  have hminus := produced_word_le hp S hn ht hdim hQ hJ hfield 211 (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simpa only [hp.caches.readoutZero] using hzero
  · simpa only [hp.caches.aliasZero] using hzero
  · simpa only [hp.caches.aliasOne] using hone
  · simpa only [hp.caches.aliasMinusOne] using hminus

end Produced

section Arithmetic

variable {base out : LeafProgram.Query.Data} {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}

/-- Actual interpolation outputs use at most Q² full coefficients; their
unary length words are charged too. The denominator is one full coefficient. -/
theorem arithmetic_word_le (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (i : Fin 768) (hi : i ∈ arithmeticPorts) :
    (out.stacks i).length ≤ 7 * (S + 1)^4 := by
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [h.low j (ringPorts_lt j hj)]
    exact produced_word_le h.produced S hn ht hdim hQ hJ hfield j hj
  · obtain ⟨h713, h714, h715, h716, h717⟩ :=
      NativeQueryPreparation.arithmetic_cache_lengths h
    have h728 := NativeQueryPreparation.arithmetic_denominator_length h
    have htwo : m.val 34 * baseWidth 3 (m.val 33) ≤ 2 * (S + 1)^4 := by
      rw [RingProgram.ternary_baseWidth]
      calc
        _ ≤ (S + 1) * (2 * (S + 1)) := by gcongr <;> omega
        _ = 2 * (S + 1)^2 := by ring
        _ ≤ 2 * (S + 1)^4 := by
          gcongr
          omega
    have hthree : m.val 21 * (m.val 34 * baseWidth 3 (m.val 33)) ≤
        2 * (S + 1)^4 := by
      rw [RingProgram.ternary_baseWidth]
      calc
        _ ≤ (S + 1) * ((S + 1) * (2 * (S + 1))) := by gcongr <;> omega
        _ = 2 * (S + 1)^3 := by ring
        _ ≤ 2 * (S + 1)^4 := by
          gcongr
          omega
    have hfour : m.val 21 * (m.val 21 * (m.val 34 * baseWidth 3 (m.val 33))) ≤
        2 * (S + 1)^4 := by
      rw [RingProgram.ternary_baseWidth]
      calc
        _ ≤ (S + 1) * ((S + 1) * ((S + 1) * (2 * (S + 1)))) := by gcongr <;> omega
        _ = 2 * (S + 1)^4 := by ring
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- A fixed sum bound for the twenty-two physically retained arithmetic words. -/
theorem arithmetic_bits_le (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S) :
    selectedStackBits arithmeticPorts out.stacks ≤ 154 * (S + 1)^4 := by
  have hb := arithmeticPorts.sum_le_card_nsmul (fun i => (out.stacks i).length)
    (7 * (S + 1)^4) (arithmetic_word_le h S hn ht hdim hQ hJ hfield)
  simpa [selectedStackBits, nsmul_eq_mul, ← Nat.mul_assoc] using hb


/-- All listed arithmetic masters include the four physical constant aliases. -/
theorem arithmetic_all_word_le
    (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (i : Fin 768) (hi : i ∈ allArithmeticPorts) :
    (out.stacks i).length ≤ 7 * (S + 1)^4 := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact arithmetic_word_le h S hn ht hdim hQ hJ hfield i hi
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have hf : out.stacks 190 = e.stacks 190 := h.low 190 (by decide)
      rw [hf]
      exact produced_alias_le h.produced S hn ht hdim hQ hJ hfield 190 (by decide)
    · have hf : out.stacks 249 = e.stacks 249 := h.low 249 (by decide)
      rw [hf]
      exact produced_alias_le h.produced S hn ht hdim hQ hJ hfield 249 (by decide)
    · have hf : out.stacks 250 = e.stacks 250 := h.low 250 (by decide)
      rw [hf]
      exact produced_alias_le h.produced S hn ht hdim hQ hJ hfield 250 (by decide)
    · have hf : out.stacks 251 = e.stacks 251 := h.low 251 (by decide)
      rw [hf]
      exact produced_alias_le h.produced S hn ht hdim hQ hJ hfield 251 (by decide)

/-- The total includes twenty-six actual words, with each retained copy charged. -/
theorem arithmetic_all_bits_le
    (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S) :
    selectedStackBits allArithmeticPorts out.stacks ≤ 182 * (S + 1)^4 := by
  have hb := allArithmeticPorts.sum_le_card_nsmul (fun i => (out.stacks i).length)
    (7 * (S + 1)^4) (arithmetic_all_word_le h S hn ht hdim hQ hJ hfield)
  simpa [selectedStackBits, nsmul_eq_mul, ← Nat.mul_assoc] using hb

/-- The arithmetic masters and preserved caller frame share one maximum.
The cleared private bank is included; unlisted lower scratch is not asserted
blank by this boundary theorem. -/
theorem arithmetic_retained_with_frame
    (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S B : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (hcaller : ∀ i, (base.stacks i).length ≤ B)
    (i : Fin 768) (hi : i ∈ arithmeticPorts ∨ 320 ≤ i.val ∧ i ≠ 699) :
    (out.stacks i).length ≤ max (7 * (S + 1)^4) B := by
  by_cases hm : i ∈ arithmeticPorts
  · exact (arithmetic_word_le h S hn ht hdim hQ hJ hfield i hm).trans (le_max_left _ _)
  have hge : 320 ≤ i.val := (hi.resolve_left hm).1
  have h699 : i ≠ 699 := (hi.resolve_left hm).2
  by_cases hlo : i.val < 340
  · rw [h.collectorFrame i hge hlo]
    exact (hcaller i).trans (le_max_right _ _)
  by_cases hpriv : i.val < 660
  · rw [h.privateEmpty i (by omega) hpriv]
    simp
  have hnout : i ∉ ([713, 714, 715, 716, 717, 728] : List (Fin 768)) := by
    intro hc
    apply hm
    apply Finset.mem_union_right
    simpa only [List.mem_cons, List.not_mem_nil, or_false,
      Finset.mem_insert, Finset.mem_singleton] using hc
  rw [h.highFrame i (by omega) h699 hnout]
  exact (hcaller i).trans (le_max_right _ _)

/-- Include all four physical aliases in the same retained caller maximum. -/
theorem arithmetic_all_retained_with_frame
    (h : LeafProgram.Query.ArithmeticOutput base out m hd M cache half e)
    (S B : ℕ) (hn : m.val 0 ≤ S) (ht : m.val 33 ≤ S) (hdim : m.val 34 ≤ S)
    (hQ : m.val 21 ≤ S) (hJ : m.val 42 ≤ S)
    (hfield : (Circuit.result Serialization.code m).val 44 ≤ S)
    (hcaller : ∀ i, (base.stacks i).length ≤ B)
    (i : Fin 768) (hi : i ∈ allArithmeticPorts ∨ 320 ≤ i.val ∧ i ≠ 699) :
    (out.stacks i).length ≤ max (7 * (S + 1)^4) B := by
  rcases hi with hi | hi
  · exact (arithmetic_all_word_le h S hn ht hdim hQ hJ hfield i hi).trans (le_max_left _ _)
  · exact arithmetic_retained_with_frame h S B hn ht hdim hQ hJ hfield hcaller i (Or.inr hi)

end Arithmetic
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingRetainedSpace
