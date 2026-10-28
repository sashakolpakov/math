import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

/-! Physical reconstruction of the exact node caches, including the sparse
ring identity and ambient shape, before accepted assignment evaluation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def lowStack : Fin 768 → Fin 896 := Fin.castAdd 128

def localRegister : Fin 16 → Fin 40 := Fin.castAdd 24

def liftLow (c : Cmd 40 768) (input output : Fin 768) : Code :=
  liftCommand c input output id lowStack

def cachePorts : List (Fin 768) :=
  LeafNodeCacheProgram.cachePorts ++ LeafNodeCacheProgram.pocket

/-- Clears stale copies, including ambient shape88, before reconstructing the
actual encoded ring identity69 and the idempotent coefficient tape143. -/
def setupLocal : Cmd 16 768 :=
  .seq (clearMany cachePorts) LeafNodeCacheProgram.localCommand

def setup : Code := liftCommand setupLocal 128 69 localRegister lowStack

def cacheStart (a : State 16 768) := clearManyState cachePorts a

def setupLocalCost (a : State 16 768) : ℕ :=
  clearManyCost cachePorts a + LeafNodeCacheProgram.localBudget (cacheStart a)

def setupCost (a : Data) : ℕ :=
  setupLocalCost (projectState localRegister lowStack a) + 1

theorem cacheStart_ready (a : State 16 768) :
    LeafNodeCacheProgram.Ready (cacheStart a).stacks := by
  intro i hi
  change i ∈ cachePorts at hi
  rw [cacheStart, clearMany_stacks, ite_eq_left hi]

theorem setupLocal_eval (a : State 16 768) :
    ∃ b, Eval setupLocal (setupLocalCost a) a b ∧
      b.stacks = LeafNodeCacheProgram.cacheTapes (cacheStart a) := by
  obtain ⟨b, he, hb⟩ := LeafNodeCacheProgram.local_eval_exact (cacheStart a) (cacheStart_ready a)
  exact ⟨b, (clearMany_eval cachePorts a).seq he, hb⟩

theorem setup_eval (a : Data) :
    ∃ b, Eval setup (setupCost a) a b ∧
      (∀ i, b.stacks (lowStack i) =
        LeafNodeCacheProgram.cacheTapes (cacheStart (projectState localRegister lowStack a)) i) ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, hb⟩ := setupLocal_eval (projectState localRegister lowStack a)
  refine ⟨embedState localRegister lowStack a b,
    eval_liftCommand_from_state setupLocal 128 69 localRegister lowStack a
      (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) he, ?_, ?_⟩
  · intro i
    rw [embedState_stack localRegister lowStack a b (Fin.castAdd_injective _ _) i, hb]
  · intro i hi
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

theorem setupLocalCost_le (a : State 16 768) (B : ℕ) (ha : WordBound B a) :
    setupLocalCost a ≤ 1100 * (B + 1) := by
  have hclear := clearManyCost_le cachePorts a B ha
  have hcache := LeafNodeCacheProgram.localBudget_le (cacheStart a) B
    (clearMany_wordBound cachePorts a B ha)
  change clearManyCost cachePorts a ≤ 21 * (2 * B + 3) at hclear
  unfold setupLocalCost
  omega

theorem setupCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    setupCost a ≤ 1100 * (B + 1) + 1 := by
  exact Nat.add_le_add_right (setupLocalCost_le _ B (fun i => ha (lowStack i))) 1

/-- The setup trace includes the finite caller return. Its polynomial local
runtime accounts for every copy and temporary at every prefix. -/
theorem setup_run_space (a : Data) (B : ℕ) (ha : WordBound B a) :
    ∃ b, Eval setup (setupCost a) a b ∧
      (∀ i, b.stacks (lowStack i) =
        LeafNodeCacheProgram.cacheTapes (cacheStart (projectState localRegister lowStack a)) i) ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) ∧
      Trace (compiled setup 128 69) (setupCost a + 1)
        (a.withPC (some (compiled setup 128 69).entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ setupCost a + 1 →
        Trace (compiled setup 128 69) prefixSteps
          (a.withPC (some (compiled setup 128 69).entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + 1100 * (B + 1) + 2 := by
  obtain ⟨b, he, hlow, hhigh⟩ := setup_eval a
  refine ⟨b, he, hlow, hhigh, compiled_halt_trace he 128 69, ?_⟩
  intro prefixSteps intermediate hp ht
  have hgrowth := trace_dataBits (compiled setup 128 69) ht
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  have hcost := setupCost_le a B ha
  omega

theorem setup_local_frame (a : State 16 768) (i : Fin 768) (hi : i ∉ cachePorts) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) i = a.stacks i := by
  have hcache : i ∉ LeafNodeCacheProgram.cachePorts := by
    intro hm
    exact hi (List.mem_append_left _ hm)
  rw [LeafNodeCacheProgram.cache_frame _ i hcache, cacheStart, clearMany_stacks,
    ite_eq_right hi]

theorem setup_direct_word (a : State 16 768) (pair : Fin 768 × Fin 768)
    (hp : pair ∈ LeafNodeCacheProgram.directCopies) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) pair.2 = a.stacks pair.1 := by
  rw [LeafNodeCacheProgram.cache_direct _ (cacheStart_ready a) pair hp,
    cacheStart, clearMany_stacks]
  have hsep : pair.1 ∉ cachePorts := by
    have hall : ∀ q ∈ LeafNodeCacheProgram.directCopies, q.1 ∉ cachePorts := by
      simp [LeafNodeCacheProgram.directCopies, cachePorts,
        LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
    exact hall pair hp
  rw [ite_eq_right hsep]

/-- All 56 arithmetic ports are restored to the original Product.idle ABI.
The other copied cache words lie outside that bank. -/
theorem setup_low (a : State 16 768)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 712) = []) :
    ∀ i : Fin 56,
      LeafNodeCacheProgram.cacheTapes (cacheStart a) (i.castAdd 712) =
        MomentsProgram.Product.tapes (MomentsProgram.Product.idle
          (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
          (a.stacks 204) (a.stacks 212) (a.stacks 243)) i := by
  intro i
  by_cases h5 : i = 5
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (194, 5) (by decide)
  by_cases h12 : i = 12
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (202, 12) (by decide)
  by_cases h17 : i = 17
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (203, 17) (by decide)
  by_cases h22 : i = 22
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (201, 22) (by decide)
  by_cases h39 : i = 39
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (204, 39) (by decide)
  by_cases h45 : i = 45
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (212, 45) (by decide)
  by_cases h46 : i = 46
  · subst i
    simpa [MomentsProgram.Product.tapes, MomentsProgram.Product.idle] using
      setup_direct_word a (243, 46) (by decide)
  have hi : i.castAdd 712 ∉ cachePorts := by
    intro hm
    simp only [Fin.ext_iff] at h5 h12 h17 h22 h39 h45 h46
    simp [cachePorts, LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hm
    omega
  rw [setup_local_frame a _ hi, hempty i]
  simp [MomentsProgram.Product.tapes, MomentsProgram.Product.idle,
    h5, h12, h17, h22, h39, h45, h46]

/-- The word69 is constructed by the actual constant encoder, including the
ambient coordinate count. No semantically supplied ring-one dictionary is used. -/
theorem setup_one_word (a : State 16 768) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) 69 = LeafNodeCacheProgram.rawOne a.stacks := by
  rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).1]
  have h128 : (cacheStart a).stacks 128 = a.stacks 128 := by
    simp [cacheStart, clearMany_stacks, cachePorts,
      LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
  have h207 : (cacheStart a).stacks 207 = a.stacks 207 := by
    simp [cacheStart, clearMany_stacks, cachePorts,
      LeafNodeCacheProgram.cachePorts, LeafNodeCacheProgram.pocket]
  simp only [LeafNodeCacheProgram.rawOne, h128, h207]

def oneEntries {n B d : ℕ} (one : RingProgram.Code (SubexpQuarticRing.Word B) d) :
    List (MomentsProgram.Product.Entry n B d) := [(Squarefree.Index.origin, one)]

theorem oneEntries_eq_constant {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    oneEntries (n:=n) one = Squarefree.Sparse.constant u J one := by
  simp [Squarefree.Sparse.constant, hu, hJ, oneEntries]

theorem oneEntries_good {n B d : ℕ} (one : RingProgram.Code (SubexpQuarticRing.Word B) d)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J) :
    NativeSemantics.Good (∅ : Finset (Fin n)) u J (oneEntries one) := by
  constructor
  · intro e he
    simp only [oneEntries, List.mem_singleton] at he
    subst e
    simp [MomentsProgram.Product.ValidKey, Squarefree.Index.origin,
      Squarefree.Index.Kept, Squarefree.Index.Valid, hu, hJ]
  · simp [oneEntries, Squarefree.Sparse.keys]

theorem setup_one_bytes (a : State 16 768) {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d)
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one) :
    LeafNodeCacheProgram.cacheTapes (cacheStart a) 69 =
      MomentsProgram.Product.bytes (oneEntries (n:=n) one) := by
  rw [setup_one_word]
  simp [LeafNodeCacheProgram.rawOne, hn, ho, HashCircuitProgram.Constant.key_eq_origin,
    oneEntries, MomentsProgram.Product.bytes, MomentsProgram.Normalize.bytes,
    Squarefree.Program.rawEntries, Squarefree.Program.encodeDictionary]

/-- The setup's retained cache bound depends on the original physical words,
not on a growing total-space envelope. All untouched caller words retain their
original bound. -/
theorem setup_cache_wordBound (a : State 16 768) (B : ℕ) (ha : WordBound B a) :
    ∀ i, (LeafNodeCacheProgram.cacheTapes (cacheStart a) i).length ≤ 4 * B + 6 := by
  intro i
  by_cases hi : i ∈ LeafNodeCacheProgram.cachePorts
  · have hcases : i = 5 ∨ i = 12 ∨ i = 17 ∨ i = 22 ∨ i = 39 ∨ i = 45 ∨
        i = 46 ∨ i = 76 ∨ i = 143 ∨ i = 88 ∨ i = 190 ∨ i = 191 ∨ i = 69 ∨ i = 167 := by
      simpa [LeafNodeCacheProgram.cachePorts] using hi
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [setup_direct_word a (194, 5) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (202, 12) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (203, 17) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (201, 22) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (204, 39) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (212, 45) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (243, 46) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (211, 76) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (281, 143) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (128, 88) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (280, 190) (by decide)]; exact (ha _).trans (by omega))
      | (rw [setup_direct_word a (128, 191) (by decide)]; exact (ha _).trans (by omega))
      | skip
    · rw [setup_one_word, LeafNodeCacheProgram.rawOne_length a]
      have hn := ha 128
      have ho := ha 207
      omega
    · rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).2]
      have hone := setup_one_word a
      rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).1] at hone
      rw [hone, LeafNodeCacheProgram.rawOne_length a]
      have hn := ha 128
      have ho := ha 207
      omega
  · rw [LeafNodeCacheProgram.cache_frame _ i hi, cacheStart, clearMany_stacks]
    split_ifs
    · simp
    · exact (ha _).trans (by omega)

theorem setup_eval_wordBound (a : Data) (B : ℕ) (ha : WordBound B a) :
    ∃ b, Eval setup (setupCost a) a b ∧ WordBound (4 * B + 6) b ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, hl, hh⟩ := setup_eval a
  refine ⟨b, he, ?_, hh⟩
  intro i
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, hl j]
    exact setup_cache_wordBound (projectState localRegister lowStack a) B
      (fun q => ha (lowStack q)) j
  · rw [hh i (by omega)]
    exact (ha _).trans (by omega)

/-- The retained cache envelope uses physical master sizes separately from the
caller frame. Repeating setup therefore preserves any common bound containing
both the frame and the fixed generated cache words. -/
theorem setup_cache_wordBound_max (a : State 16 768) (A M : ℕ)
    (ha : WordBound A a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies, (a.stacks p.1).length ≤ M)
    (hn : (a.stacks 128).length ≤ M) (ho : (a.stacks 207).length ≤ M) :
    ∀ i, (LeafNodeCacheProgram.cacheTapes (cacheStart a) i).length ≤ max A (4 * M + 6) := by
  have hone : (LeafNodeCacheProgram.rawOne a.stacks).length ≤ 4 * M + 6 := by
    rw [LeafNodeCacheProgram.rawOne_length]
    omega
  intro i
  by_cases hi69 : i = 69
  · subst i
    rw [setup_one_word]
    exact hone.trans (Nat.le_max_right _ _)
  by_cases hi167 : i = 167
  · subst i
    rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).2]
    have he := setup_one_word a
    rw [(LeafNodeCacheProgram.cache_one (cacheStart a)).1] at he
    rw [he]
    exact hone.trans (Nat.le_max_right _ _)
  by_cases hi : ∃ p ∈ LeafNodeCacheProgram.directCopies, p.2 = i
  · obtain ⟨p, hp, rfl⟩ := hi
    rw [setup_direct_word a p hp]
    exact (hcopy p hp).trans (le_trans (by omega : M ≤ 4 * M + 6) (Nat.le_max_right _ _))
  · have hnot : i ∉ LeafNodeCacheProgram.cachePorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false, Prod.exists, Prod.mk.injEq] at hi
      simp only [LeafNodeCacheProgram.cachePorts, List.mem_cons, List.not_mem_nil, or_false]
      aesop
    rw [LeafNodeCacheProgram.cache_frame _ i hnot, cacheStart, clearMany_stacks]
    split_ifs
    · simp
    · exact (ha i).trans (Nat.le_max_left _ _)

theorem setup_eval_wordBound_max (a : Data) (A M : ℕ)
    (ha : WordBound A a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies, (a.stacks (lowStack p.1)).length ≤ M)
    (hn : (a.stacks 128).length ≤ M) (ho : (a.stacks 207).length ≤ M) :
    ∃ b, Eval setup (setupCost a) a b ∧ WordBound (max A (4 * M + 6)) b ∧
      (∀ i : Fin 896, 768 ≤ i.val → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, hl, hh⟩ := setup_eval a
  refine ⟨b, he, ?_, hh⟩
  intro i
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, hl j]
    exact setup_cache_wordBound_max (projectState localRegister lowStack a) A M
      (fun q => ha (lowStack q)) hcopy hn ho j
  · rw [hh i (by omega)]
    exact (ha i).trans (Nat.le_max_left _ _)

/-- Concrete setup produces the same identity dictionary used by subsequent
factor semantics, with an exact frame for all non-cache caller storage. -/
theorem setup_context (a : Data) {n B d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word B) d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one) :
    ∃ b, Eval setup (setupCost a) a b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) =
        MomentsProgram.Product.tapes (MomentsProgram.Product.idle
          (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
          (a.stacks 204) (a.stacks 212) (a.stacks 243)) i) ∧
      b.stacks 69 = MomentsProgram.Product.bytes (oneEntries (n:=n) one) ∧
      NativeSemantics.Good (∅ : Finset (Fin n)) u J (oneEntries one) ∧
      ∀ i : Fin 896, i ∉ cachePorts.map lowStack → b.stacks i = a.stacks i := by
  obtain ⟨b, he, hl, hh⟩ := setup_eval a
  let initial := projectState localRegister lowStack a
  refine ⟨b, he, ?_, ?_, oneEntries_good one u J hu hJ, ?_⟩
  · intro i
    have hi := hl (i.castAdd 712)
    exact hi.trans (setup_low initial hempty i)
  · exact (hl 69).trans (setup_one_bytes initial one hn ho)
  · intro i hi
    by_cases hlt : i.val < 768
    · let j : Fin 768 := ⟨i.val, hlt⟩
      have hj : lowStack j = i := Fin.ext rfl
      have hmem : j ∉ cachePorts := by
        intro hjmem
        exact hi (List.mem_map.mpr ⟨j, hjmem, hj⟩)
      rw [← hj, hl j, setup_local_frame initial j hmem]
      rfl
    · exact hh i (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
