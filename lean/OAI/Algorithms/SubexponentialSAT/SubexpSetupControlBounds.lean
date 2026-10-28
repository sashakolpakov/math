import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec
import OAI.Algorithms.SubexponentialSAT.SubexpSetupControl
import OAI.Algorithms.SubexponentialSAT.SubexpSetupCounters

namespace OAI.Algorithms

/-! Linear time and word bounds for the existing concrete setup controls. -/

noncomputable section

namespace SubexponentialSAT.SubexpSetupControlBounds

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupProgram SubexpSetupBoundSpec
open scoped BigOperators

private abbrev LinearWitness {r s : ℕ} (cmd : Cmd r s) (C : ℕ) : Prop :=
  ∀ B a, WordBound B a → ∃ t b, Eval cmd t a b ∧
    t ≤ C * (B + 1) ∧ WordBound (C * (B + 1)) b

private theorem total_of_linear {r s C : ℕ} {cmd : Cmd r s}
    (h : LinearWitness cmd C) (a : State r s) : ∃ t b, Eval cmd t a b := by
  let B := ∑ i : Fin s, (a.stacks i).length
  have ha : WordBound B a := by
    intro i
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length)) (Finset.mem_univ i)
  obtain ⟨t, b, he, _, _⟩ := h B a ha
  exact ⟨t, b, he⟩

private theorem envelope_of_linear {r s C : ℕ} {cmd : Cmd r s}
    (port : Fin s) (hC : 1 ≤ C) (h : LinearWitness cmd C) :
    ∃ K q : ℕ, 1 ≤ K ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval cmd t a b →
        t ≤ K * (B + P + 1) ^ q ∧ WordBound (K * (B + P + 1) ^ q) b := by
  refine ⟨C, 1, hC, by decide, ?_⟩
  intro B P a t b ha he
  apply bounds_of_witness port _ he
  obtain ⟨u, out, hu, ht, hw⟩ := h B a ha
  have hb : C * (B + 1) ≤ C * (B + P + 1) ^ 1 := by
    simp only [pow_one]
    exact Nat.mul_le_mul_left C (by omega)
  exact ⟨u, out, hu, ht.trans hb, wordBound_mono hw hb⟩

private theorem run_with_wordBound {r s B C t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) (ht : t ≤ C * (B + 1)) :
    t ≤ (C + 1) * (B + 1) ∧ WordBound ((C + 1) * (B + 1)) b := by
  constructor
  · nlinarith
  · exact wordBound_mono (eval_wordBound ha he) (by nlinarith)

theorem counterStage_bounded (c : Config) (increment : Bool) (source target : Fin 32)
    (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (counterStage c increment source target) t a b ∧
      t ≤ 200 * (B + 1) ∧ WordBound (200 * (B + 1)) b := by
  let hs : 2 < helperSize c := small_fits c (by decide)
  have ha' : WordBound (B + 1) a := wordBound_mono ha (by omega)
  have hout : WordBound (B + 1) (counterOut increment (a.stacks (persistent c source))) := by
    intro i
    fin_cases i
    · simpa [counterOut, StructuredProgram.ioState] using
        (CounterPrograms.ripple_length_le increment (a.stacks (persistent c source))).trans
          (Nat.add_le_add_right (ha (persistent c source)) 1)
    · simp [counterOut, StructuredProgram.ioState]
  have hc := stageCost_le c (registerPort (show 3 ≤ 9 by decide)) hs
    [(persistent c source, 0)] [(0, persistent c target)] a
    (counterOut increment (a.stacks (persistent c source)))
    (8 * (a.stacks (persistent c source)).length + 8) (B + 1)
    (by simp) (by simp) (by simp) (by simp) ha' hout
  have hsbound := storageOverhead_linear 2 1 1 (B + 1)
  have hlen := ha (persistent c source)
  have hcost : counterBound c increment source target a ≤ 200 * (B + 1) := by
    change counterBound c increment source target a ≤ _ at hc
    simp only [List.length_singleton] at hc
    norm_num at hsbound
    nlinarith
  have hreturn := returned_wordBound c (registerPort (show 3 ≤ 9 by decide)) hs
    [(persistent c source, 0)] [(0, persistent c target)] a
    (counterOut increment (a.stacks (persistent c source))) (B + 1)
    (by simp) (by simp) (by simp) (by simp) ha' hout
  obtain ⟨t, ht, he, _, _⟩ := counterStage_eval c increment source target a
  exact ⟨t, _, he, ht.trans hcost, wordBound_mono hreturn (by omega)⟩

private def guardStart (c : Config)
    (inputs : List (Fin (stackCount c) × Fin 6)) (a : SetupState c) : State 9 6 :=
  project guardRegister (workPort c (small_fits c (by decide)))
    (prepared c (small_fits c (by decide)) inputs a)

private theorem guardStart_wordBound (c : Config)
    (inputs : List (Fin (stackCount c) × Fin 6)) (a : SetupState c) (B : ℕ)
    (hi : ∀ p ∈ inputs, Protected c p.1) (hd : (inputs.map Prod.snd).Nodup)
    (ha : WordBound B a) : WordBound B (guardStart c inputs a) := by
  intro i
  exact prepared_wordBound c (small_fits c (by decide)) inputs a B hi hd ha
    (workPort c (small_fits c (by decide)) i)

private theorem guardStage_bounded (c : Config) (core : Cmd 9 6)
    (inputs : List (Fin (stackCount c) × Fin 6)) (B : ℕ) (a : SetupState c)
    (hi : ∀ p ∈ inputs, Protected c p.1) (hd : (inputs.map Prod.snd).Nodup)
    (hlen : inputs.length ≤ 6) (ha : WordBound B a)
    (hrun : ∃ t out, Eval core t (guardStart c inputs a) out ∧ t ≤ 100 * (B + 1)) :
    ∃ t b, Eval (stage c (compiled core 0 1) guardRegister
        (small_fits c (by decide)) inputs []) t a b ∧
      t ≤ 20000 * (B + 1) ∧ WordBound (20000 * (B + 1)) b := by
  obtain ⟨t, out, he, ht⟩ := hrun
  let hs : 6 < helperSize c := small_fits c (by decide)
  let H := 101 * (B + 1)
  have hstart := guardStart_wordBound c inputs a B hi hd ha
  have hout : WordBound H out := wordBound_mono (eval_wordBound hstart he) (by dsimp [H]; omega)
  have haH : WordBound H a := wordBound_mono ha (by dsimp [H]; omega)
  have hstage := stage_eval c (compiled core 0 1) guardRegister guardRegister_injective
    hs inputs [] a (guardStart c inputs a) out hi (by simp) rfl (compiled_halt_trace he 0 1)
  have hc := stageCost_le c guardRegister hs inputs [] a out (t + 1) H hi
    (by simp) hd (by simp) haH hout
  have hstorage := storageOverhead_linear 6 inputs.length 0 H
  have hcoeff : 6 * 6 + 7 * inputs.length + 10 * 0 + 21 ≤ 99 := by omega
  have hmult := Nat.mul_le_mul_right (H + 1) hcoeff
  have hcost : stageCost c guardRegister hs inputs [] a out (t + 1) ≤ 20000 * (B + 1) := by
    simp only [List.length_nil] at hc
    dsimp [H] at *
    nlinarith
  have hreturn := returned_wordBound c guardRegister hs inputs [] a out H hi
    (by simp) hd (by simp) haH hout
  exact ⟨_, _, hstage, hcost, wordBound_mono hreturn (by dsimp [H]; omega)⟩

theorem early_bounded (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (early c) t a b ∧ t ≤ 20000 * (B + 1) ∧ WordBound (20000 * (B + 1)) b := by
  let inputs : List (Fin (stackCount c) × Fin 6) := [(persistent c 4, 0)]
  have hi : ∀ p ∈ inputs, Protected c p.1 := by simp [inputs]
  have hd : (inputs.map Prod.snd).Nodup := by simp [inputs]
  have hs := guardStart_wordBound c inputs a B hi hd ha
  have hz : (guardStart c inputs a).stacks 1 = [] := by
    have hnone : ∀ p ∈ inputs, (1 : Fin 6) ≠ p.2 := by
      intro p hp
      simp only [inputs, List.mem_singleton] at hp
      subst p
      change (1 : Fin 6) ≠ 0
      decide
    dsimp only [guardStart, project, Function.comp_apply]
    exact prepared_empty c (s := 6) (small_fits c (by decide)) inputs a 1 hnone
  obtain ⟨out, he, _, _, _⟩ := SubexpGuardProgram.earlyGuard_eval (guardStart c inputs a) hz
  apply guardStage_bounded c SubexpGuardProgram.earlyGuard inputs B a hi hd (by simp [inputs]) ha
  refine ⟨_, out, he, ?_⟩
  have hm : max ((guardStart c inputs a).stacks 0).length 6 ≤ B + 6 :=
    max_le (by have := hs 0; omega) (by omega)
  dsimp [SubexpGuardProgram.earlyGuardCost]
  omega

theorem readyGuard_bounded (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (readyGuard c) t a b ∧
      t ≤ 20000 * (B + 1) ∧ WordBound (20000 * (B + 1)) b := by
  let inputs : List (Fin (stackCount c) × Fin 6) :=
    [(persistent c 4, 0), (persistent c 28, 1), (persistent c 26, 2),
      (persistent c 27, 3), (persistent c 19, 4), (persistent c 20, 5)]
  have hi : ∀ p ∈ inputs, Protected c p.1 := by
    intro p hp
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact persistent_protected c _
  have hd : (inputs.map Prod.snd).Nodup := by simp [inputs]
  have hs := guardStart_wordBound c inputs a B hi hd ha
  have hpair (j : Fin 3) : SubexpGuardProgram.pairCost j (guardStart c inputs a) ≤ 10 * B + 8 := by
    have hm := max_le (hs (SubexpGuardProgram.pairStack j 0)) (hs (SubexpGuardProgram.pairStack j 1))
    dsimp [SubexpGuardProgram.pairCost]
    omega
  obtain ⟨out, he, _⟩ := SubexpGuardProgram.guard_eval (guardStart c inputs a)
  apply guardStage_bounded c SubexpGuardProgram.guard inputs B a hi hd (by simp [inputs]) ha
  refine ⟨_, out, he, ?_⟩
  have h0 := hpair 0
  have h1 := hpair 1
  have h2 := hpair 2
  dsimp [SubexpGuardProgram.guardCost]
  omega

theorem cutoff_bounded (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (cutoff c) t a b ∧ t ≤ 20 * (B + 1) ∧ WordBound (20 * (B + 1)) b := by
  let mid := clearManyState [persistent c 28] a
  let b := SubexpGuardProgram.loadThirtyTwoState (0 : Fin 16) (persistent c 28) mid
  have he : Eval (cutoff c) (clearManyCost [persistent c 28] a + 8) a b :=
    .seq (clearMany_eval _ a) (.base (SubexpGuardProgram.loadThirtyTwo_eval _ _ mid))
  have hc := clearManyCost_le [persistent c 28] a B ha
  have ht : clearManyCost [persistent c 28] a + 8 ≤ 19 * (B + 1) := by
    simp only [List.length_singleton, one_mul] at hc
    omega
  exact ⟨_, b, he, run_with_wordBound ha he ht⟩

theorem colors_bounded (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (colors c) t a b ∧ t ≤ 20 * (B + 1) ∧ WordBound (20 * (B + 1)) b := by
  let ps := [temporary c, persistent c 21]
  let mid := clearManyState ps a
  let b := copyState (persistent c 4) (persistent c 21) mid
  have hne : persistent c 4 ≠ persistent c 21 := by
    intro he
    have hv := congrArg (fun x : Fin (stackCount c) => x.val) he
    change helperSize c + thresholdCount c + 4 = helperSize c + thresholdCount c + 21 at hv
    omega
  have htmp4 := protected_ne_temporary c (persistent_protected c 4)
  have htmp21 := protected_ne_temporary c (persistent_protected c 21)
  have hz : mid.stacks (temporary c) = [] := by simp [mid, ps, clearMany_stacks]
  have he : Eval (colors c)
      (clearManyCost ps a + (7 * (mid.stacks (persistent c 4)).length + 5 + 0)) a b :=
    .seq (clearMany_eval ps a) (.seq (copy_eval _ _ _ mid hne htmp4 htmp21.symm hz) (.base (.skip b)))
  have hc := clearManyCost_le ps a B ha
  have hm := clearMany_wordBound ps a B ha (persistent c 4)
  have ht : clearManyCost ps a + (7 * (mid.stacks (persistent c 4)).length + 5 + 0) ≤ 19 * (B + 1) := by
    have hplen : ps.length = 2 := rfl
    rw [hplen] at hc
    change (mid.stacks (persistent c 4)).length ≤ B at hm
    omega
  exact ⟨_, b, he, run_with_wordBound ha he ht⟩

theorem cleanup_bounded (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (clearMany (workspacePorts c)) t a b ∧
      t ≤ (3 * (workspacePorts c).length + 2) * (B + 1) ∧
      WordBound ((3 * (workspacePorts c).length + 2) * (B + 1)) b := by
  have he := clearMany_eval (workspacePorts c) a
  have hc := clearManyCost_le (workspacePorts c) a B ha
  have hm := Nat.mul_le_mul_left (workspacePorts c).length (show 2 * B + 3 ≤ 3 * (B + 1) by omega)
  have ht : clearManyCost (workspacePorts c) a ≤ (3 * (workspacePorts c).length + 1) * (B + 1) := by
    nlinarith
  exact ⟨_, _, he, run_with_wordBound ha he ht⟩

theorem counterStage_total (c : Config) (increment : Bool) (source target : Fin 32) (a : SetupState c) :
    ∃ t b, Eval (counterStage c increment source target) t a b :=
  total_of_linear (counterStage_bounded c increment source target) a

theorem early_total (c : Config) (a : SetupState c) : ∃ t b, Eval (early c) t a b :=
  total_of_linear (early_bounded c) a

theorem readyGuard_total (c : Config) (a : SetupState c) : ∃ t b, Eval (readyGuard c) t a b :=
  total_of_linear (readyGuard_bounded c) a

theorem cutoff_total (c : Config) (a : SetupState c) : ∃ t b, Eval (cutoff c) t a b :=
  total_of_linear (cutoff_bounded c) a

theorem colors_total (c : Config) (a : SetupState c) : ∃ t b, Eval (colors c) t a b :=
  total_of_linear (colors_bounded c) a

theorem cleanup_total (c : Config) (a : SetupState c) : ∃ t b, Eval (clearMany (workspacePorts c)) t a b :=
  total_of_linear (cleanup_bounded c) a

theorem counterStage_envelope (c : Config) (increment : Bool) (source target : Fin 32) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval (counterStage c increment source target) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 200) (persistent c 0) (by decide) (counterStage_bounded c increment source target)

theorem early_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b, WordBound B a → Eval (early c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 20000) (persistent c 0) (by decide) (early_bounded c)

theorem readyGuard_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b, WordBound B a → Eval (readyGuard c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 20000) (persistent c 0) (by decide) (readyGuard_bounded c)

theorem cutoff_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b, WordBound B a → Eval (cutoff c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 20) (persistent c 0) (by decide) (cutoff_bounded c)

theorem colors_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b, WordBound B a → Eval (colors c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 20) (persistent c 0) (by decide) (colors_bounded c)

theorem cleanup_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval (clearMany (workspacePorts c)) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b :=
  envelope_of_linear (C := 3 * (workspacePorts c).length + 2)
    (persistent c 0) (by omega) (cleanup_bounded c)

end SubexponentialSAT.SubexpSetupControlBounds

end

end OAI.Algorithms
