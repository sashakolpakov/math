import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPreparationFrames
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCandidateContract

namespace OAI.Algorithms

/-! # Actual preparation of every input to the quartic candidate search -/

namespace SubexponentialSAT.SubexpQuarticPreparation

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpEnumerationPayload SubexpAlphabetProgram SubexpScanPrimitives
open SubexpQuarticProducerControl SubexpQuarticCallback SubexpQuarticScanInvariant
open SubexpQuarticCandidateContract SubexpQuarticPreparationFrames

abbrev Data := SubexpQuarticProducerControl.Data

def inputState (regs : Fin 14 → Bool) (bits : List Bool) : Data :=
  ⟨regs, fun j => if j = 34 then bits else []⟩

def primeModulus (p : ℕ) : SubexpPreparedQuartic.Modulus p 1 where
  bits := primeWord p
  length_le := by simp [baseWidth, scalarWidth]
  value := by simpa only [Nat.pow_one, ← CounterPrograms.value_eq_toNat] using primeWord_value p

def cost (p inputLength : ℕ) [Fact p.Prime] : ℕ :=
  9 * inputLength + 21 + 2 * (7 * scalarWidth p + 5) +
  (p + 1) * (60 * scalarWidth p + 60) +
  SubexpOrderedTupleProgram.cost ((QuarticSearch.elements p).map (scalarCode p).block) 2 + 5 +
  SubexpOrderedTupleProgram.cost ((QuarticSearch.elements p).map (scalarCode p).block) 4 + 5 +
  110 * (scalarWidth p + 1)

theorem prepare_eval (p : ℕ) [Fact p.Prime] (bits : List Bool) (regs : Fin 14 → Bool)
    (hvalue : CounterPrograms.value bits = p) :
    ∃ n next, n ≤ cost p bits.length ∧
      Eval prepare n (inputState regs bits) next ∧
      SearchReady p (primeModulus p) next ∧
      next.stacks 28 = ProgramEncoding.encodeRecords (SubexpQuarticSelector.candidateRecords p) ∧
      next.stacks 29 = [] := by
  let initial := inputState regs bits
  have hi : Blank [34] initial := by
    intro j hj
    simp [initial, inputState, show j ≠ 34 by simpa using hj]
  obtain ⟨n₀, norm, hn₀, he₀, hnorm34, hnorm0, hnorm1, hnormFrame⟩ :=
    SubexpQuarticInitialCalls.normalize_call p initial bits rfl hvalue
      (hi 0 (by decide)) (hi 1 (by decide))
  have hnorm : Blank [34] norm := blank_normalized initial norm hi hnorm0 hnorm1 hnormFrame
  let a := afterCopy norm 34 19 0 1
  have he₁ := SubexpScanPrimitives.copy_eval norm 34 19 27 0 1
    (by decide) (by decide) (by decide) (by decide) (hnorm 27 (by decide))
  have ha : Blank [19, 34] a := blank_copy [34] norm 34 19 hnorm
  have ha34 : a.stacks 34 = primeWord p := by
    simpa [a, afterCopy, StackRoutines.copyStacks] using hnorm34
  have ha19 : a.stacks 19 = primeWord p := by
    simp [a, afterCopy, StackRoutines.copyStacks, hnorm34, hnorm 19 (by decide)]
  let b := afterCopy a 34 31 0 1
  have he₂ := SubexpScanPrimitives.copy_eval a 34 31 27 0 1
    (by decide) (by decide) (by decide) (by decide) (ha 27 (by decide))
  have hb : Blank [31, 19, 34] b := blank_copy [19, 34] a 34 31 ha
  have hb34 : b.stacks 34 = primeWord p := by
    simpa [b, afterCopy, StackRoutines.copyStacks] using ha34
  have hb19 : b.stacks 19 = primeWord p := by
    simpa [b, afterCopy, StackRoutines.copyStacks] using ha19
  have hb31 : b.stacks 31 = primeWord p := by
    simp [b, afterCopy, StackRoutines.copyStacks, ha34, ha 31 (by decide)]
  obtain ⟨n₃, alph, hn₃, he₃, halph25, halph22, halph0, halph1, halph2,
      _, halph34, halphFrame⟩ :=
    SubexpQuarticInitialCalls.alphabet_call p b hb34 (hb 22 (by decide))
      (hb 0 (by decide)) (hb 1 (by decide)) (hb 2 (by decide)) (hb 25 (by decide))
  have halph : Blank [25, 31, 19, 34] alph :=
    blank_alphabet b alph hb halph0 halph1 halph2 halph22 halphFrame
  let words := (QuarticSearch.elements p).map (scalarCode p).block
  have hsmall₁ : ∀ j ∈ ([25, 31, 19, 34] : List (Fin 35)), 7 ≤ j.val := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have hinput₂ := tuple_input [25, 31, 19, 34] alph 26 words halph hsmall₁ (by decide) halph25
  obtain ⟨n₄, pairs, hn₄, hpairs, he₄⟩ :=
    SubexpQuarticTupleCalls.call_eval 2 26 (Or.inl rfl) words alph hinput₂
  let pairsClean := afterMarkerClear pairs
  have he₅ := clear_marker_eval pairs hpairs.marker
  have hpairsBlank : Blank [26, 25, 31, 19, 34] pairsClean :=
    blank_tuple [25, 31, 19, 34] alph pairs 2 26 words halph hsmall₁ (by decide) hpairs
  have hpairs25 : pairsClean.stacks 25 = ProgramEncoding.encodeRecords words :=
    (afterMarkerClear_frame pairs 25 (by decide)).trans hpairs.alphabet
  have hsmall₂ : ∀ j ∈ ([26, 25, 31, 19, 34] : List (Fin 35)), 7 ≤ j.val := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
  have hinput₄ := tuple_input [26, 25, 31, 19, 34] pairsClean 28 words hpairsBlank hsmall₂
    (by decide) hpairs25
  obtain ⟨n₆, quartics, hn₆, hquartics, he₆⟩ :=
    SubexpQuarticTupleCalls.call_eval 4 28 (Or.inr rfl) words pairsClean hinput₄
  let ready := afterMarkerClear quartics
  have he₇ := clear_marker_eval quartics hquartics.marker
  have hblank : Blank [28, 26, 25, 31, 19, 34] ready :=
    blank_tuple [26, 25, 31, 19, 34] pairsClean quartics 4 28 words
      hpairsBlank hsmall₂ (by decide) hquartics
  have hreadyFrame (j : Fin 35) (hj : 7 ≤ j.val)
      (hj25 : j ≠ 25) (hj26 : j ≠ 26) (hj28 : j ≠ 28)
      (hj34 : j ≠ 34) (hj22 : j ≠ 22) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2) :
      ready.stacks j = b.stacks j := by
    have hj3 : j ≠ 3 := by intro he; have := congrArg Fin.val he; omega
    exact (afterMarkerClear_frame quartics j hj3).trans
      ((hquartics.stack_frame j hj hj25 hj28).trans
        ((afterMarkerClear_frame pairs j hj3).trans
          ((hpairs.stack_frame j hj hj25 hj26).trans
            (halphFrame j hj34 hj22 hj0 hj1 hj2 hj25))))
  have hready19 : ready.stacks 19 = primeWord p :=
    (hreadyFrame 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb19
  have hready31 : ready.stacks 31 = primeWord p :=
    (hreadyFrame 31 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb31
  have hready34 : (ready.stacks 34).length = scalarWidth p := by
    rw [afterMarkerClear_frame quartics 34 (by decide),
      hquartics.stack_frame 34 (by decide) (by decide) (by decide),
      afterMarkerClear_frame pairs 34 (by decide),
      hpairs.stack_frame 34 (by decide) (by decide) (by decide)]
    exact halph34
  have hbanks : ∀ j ∈ SubexpQuarticBootstrap.bankPorts, ready.stacks j = [] := by
    intro j hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    apply hblank
    have hi := i.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro he
    rcases he with he | he | he | he | he | he <;>
      have hval := congrArg Fin.val he <;>
      simp only [SubexpQuarticBootstrap.bankPort, Fin.val_castAdd] at hval <;> omega
  obtain ⟨n₈, next, hn₈, he₈, hnext6, hnext22, hnextWidth, hnextFrame, _⟩ :=
    SubexpQuarticBootstrap.command_eval ready (primeWord p) hready31 hbanks
      (hblank 22 (by decide)) (by simpa using (Fact.out : p.Prime).pos)
  have hafter (j : Fin 35) (hj : j ∉ SubexpQuarticBootstrap.bankPorts) :
      next.stacks j = ready.stacks j := hnextFrame j hj
  have hwidth (i : Fin 14) : (next.stacks (bankPort i)).length = baseWidth p 1 := by
    simpa only [SubexpQuarticCallback.bankPort, SubexpQuarticBootstrap.bankPort,
      baseWidth, one_mul, scalarWidth, primeWord_length] using hnextWidth i
  let bank : Fin 14 → Word (baseWidth p 1) := fun i => ⟨next.stacks (bankPort i), hwidth i⟩
  have hrep : Represents p 1 (primeModulus p) next bank := by
    refine ⟨fun _ => rfl, ?_, hnext22⟩
    intro i
    fin_cases i
    · exact (hafter 14 (by decide)).trans (hblank 14 (by decide))
    · exact (hafter 15 (by decide)).trans (hblank 15 (by decide))
    · exact (hafter 16 (by decide)).trans (hblank 16 (by decide))
    · exact (hafter 17 (by decide)).trans (hblank 17 (by decide))
    · exact (hafter 18 (by decide)).trans (hblank 18 (by decide))
    · exact (hafter 19 (by decide)).trans hready19
    · exact (hafter 20 (by decide)).trans (hblank 20 (by decide))
    · exact (hafter 21 (by decide)).trans (hblank 21 (by decide))
  have hminus : baseValue p (bank 6) = -1 := by
    have hv := SubexpQuarticBootstrap.decremented_value (primeWord p) p
      (Fact.out : p.Prime).pos
      (by simpa only [← CounterPrograms.value_eq_toNat] using primeWord_value p)
    change (BinaryArithmetic.toNat (next.stacks 6) : ZMod p) = -1
    rw [hnext6, hv, Nat.cast_sub (Nat.succ_le_of_lt (Fact.out : p.Prime).pos)]
    simp
  have hready : SearchReady p (primeModulus p) next := by
    refine ⟨⟨coefficientValue p bank, bank, hrep, hminus, rfl, ?_, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hafter 30 (by decide)).trans (hblank 30 (by decide))
    · exact (hafter 32 (by decide)).trans (hblank 32 (by decide))
    · rw [hafter 31 (by decide), hready31, primeWord_length]
      simp [baseWidth, scalarWidth]
    · exact (hafter 25 (by decide)).trans
        ((afterMarkerClear_frame quartics 25 (by decide)).trans hquartics.alphabet)
    · exact (hafter 26 (by decide)).trans
        ((afterMarkerClear_frame quartics 26 (by decide)).trans
          (hquartics.pair_table_preserved.trans
            ((afterMarkerClear_frame pairs 26 (by decide)).trans hpairs.selected_output)))
    · exact (hafter 23 (by decide)).trans (hblank 23 (by decide))
    · exact (hafter 24 (by decide)).trans (hblank 24 (by decide))
    · exact (hafter 27 (by decide)).trans (hblank 27 (by decide))
    · rw [hafter 33 (by decide), hblank 33 (by decide)]
      simp
    · rw [hafter 34 (by decide), hready34]
      simp [baseWidth, scalarWidth]
  refine ⟨n₀ + ((7 * scalarWidth p + 5) + ((7 * scalarWidth p + 5) +
      (n₃ + (n₄ + (5 + (n₆ + (5 + (n₈ + 0)))))))), next, ?_, ?_, hready, ?_, ?_⟩
  · dsimp [cost]
    dsimp only [words] at hn₄ hn₆
    rw [primeWord_length] at hn₈
    omega
  · rw [hnorm34, primeWord_length] at he₁
    rw [ha34, primeWord_length] at he₂
    exact Eval.seq he₀ (Eval.seq he₁ (Eval.seq he₂ (Eval.seq he₃ (Eval.seq he₄
      (Eval.seq he₅ (Eval.seq he₆ (Eval.seq he₇ (Eval.seq he₈ (Eval.base (.skip next))))))))))
  · exact (hafter 28 (by decide)).trans
      ((afterMarkerClear_frame quartics 28 (by decide)).trans hquartics.selected_output)
  · exact (hafter 29 (by decide)).trans (hblank 29 (by decide))

end SubexponentialSAT.SubexpQuarticPreparation

end OAI.Algorithms
