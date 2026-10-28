import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadOrder
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource

/-! Semantic correctness of the concrete head accumulator. Native dictionary
witnesses are retained only for the current partial sum, and their meaning is
proved using the actual finite-ring normalization program. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators

/-- Every actual addition-and-reset execution puts the sum of the two decoded
arrays on853. This also covers an empty or zero-valued assignment product. -/
theorem accumulate_decode {R : Type*} [CommRing R]
    (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J steps : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a e : Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
    (he : Eval accumulate steps a e) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    ∃ result : List (Product.Entry n (baseWidth p t) d),
      Good ∅ u J result ∧ e.stacks 853 = Product.bytes result ∧
      rawValue u J f result = rawValue u J f seed + rawValue u J f source ∧
      e.stacks 854 = [] ∧ (∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) = []) ∧
      ∀ i, i ∉ FactorEnvironment.environmentPorts → i ≠ 853 → i ≠ 854 →
        e.stacks i = a.stacks i := by
  dsimp only
  obtain ⟨nt, b, _, hb, hg, hstacks, hclean, _⟩ := accumulate_eval p t M cache
    source seed hsource hseed a width degree zero table uCap zCap hd hw hlow
    hseedWord hsourceWord hs0 hs1
  have heq := Eval.final_unique (853 : Fin 896) he hb
  subst e
  refine ⟨Normalize.run p t M cache source seed, hg, ?_, ?_, ?_, hclean, ?_⟩
  · simp [hstacks]
  · rw [normalize_dense p t M cache scalar basis u J source seed hseed.nodup, add_comm]
  · simp [hstacks]
  · intro i hi h853 h854
    simp [hstacks, h853, h854, FactorEnvironment.reset_stacks, hi]

/-- The mathematical partial-sum invariant advances by the actual decoded
addition, without choosing a synthetic implementation of an assignment. -/
theorem normalized_partial_sum {R : Type*} [CommRing R]
    (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J i : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hseed : Good ∅ u J seed) (contribution : ℕ → Dense R u J)
    (hsource : rawValue u J
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) source = contribution i)
    (hpartial : rawValue u J
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) seed =
      ∑ j ∈ Finset.range i, contribution j) :
    rawValue u J (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (Normalize.run p t M cache source seed) =
      ∑ j ∈ Finset.range (i + 1), contribution j := by
  rw [normalize_dense p t M cache scalar basis u J source seed hseed.nodup,
    hsource, hpartial, Finset.sum_range_succ, add_comm]

/-- The first semantic loop state is produced by the paid cleanup and seed.
The head accumulator is the actual empty dictionary, and only the named
counter words are installed in addition to the reclaimed workspace. -/
theorem initial_stacks (a : Data) (h : ℕ)
    (hshape : a.stacks 651 = List.replicate h false) :
    (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))).stacks =
      Function.update (Function.update (Function.update (HeadSumAssembly.cleared a).stacks
        859 (List.replicate h false)) 860 (List.replicate h false ++ [true])) 853 [] := by
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false := by
    rw [HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)]
    exact hshape
  have hc := HeadSumAssembly.cleared_controller a 859 (by decide)
  have hs := HeadSumAssembly.cleared_controller a 861 (by decide)
  have he := seeded_stacks (HeadSumAssembly.cleared a) h hshape' hc hs
  have hz : (seeded (HeadSumAssembly.cleared a)).stacks 861 = [] := by simp [he, hs]
  rw [CounterForPrograms.testResult_stacks fuelPorts _ hz, he]

/-- The paid initial state restores the compact boundary used between all
assignments. The transient source-prefix envelope is not fed into this bound. -/
theorem initial_word_bound (a : Data) (h P : ℕ)
    (hshape : a.stacks 651 = List.replicate h false)
    (ha : ∀ i, (a.stacks i).length ≤ P) (hh : h + 1 ≤ P) :
    ∀ i, ((CounterForPrograms.testResult fuelPorts
      (seeded (HeadSumAssembly.cleared a))).stacks i).length ≤ P := by
  have hclear := HeadSumAssembly.clearWork_prefix
    (HeadSumAssembly.clearWork_eval a) ha
  have hb : ∀ i, ((HeadSumAssembly.cleared a).stacks i).length ≤ P :=
    hclear _ _ le_rfl (compiled_trace (HeadSumAssembly.clearWork_eval a) 860 860)
  intro i
  rw [initial_stacks a h hshape]
  by_cases h853 : i = 853
  · subst i
    simp
  by_cases h860 : i = 860
  · subst i
    simpa using hh
  by_cases h859 : i = 859
  · subst i
    simp
    omega
  simpa [h853, h860, h859] using hb i


/-- Candidate increment and fuel decrement restore the same compact boundary,
including the final overflow word that is never passed to the evaluator. -/
theorem advance_word_bound {h i P : ℕ} {a b : Data} (hc : Cursor h i a)
    (hp : 0 < CounterPrograms.value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) (hb : ∀ j, (b.stacks j).length ≤ P)
    (hh : h + 1 ≤ P) :
    ∀ j, ((CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts b)).stacks j).length ≤ P := by
  have hn := body_cursor_next hc hp hw hf hs
  intro j
  by_cases h859 : j = 859
  · subst j
    exact hn.wordWidth.trans hh
  by_cases h860 : j = 860
  · subst j
    exact hn.fuelWidth.le.trans hh
  by_cases h861 : j = 861
  · subst j
    simp [hn.scratch]
  rw [← CounterForPrograms.nextState_outside fuelPorts
      (Counters.incrementResult cursorPorts b) j h860 h861,
    Counters.incrementResult_stacks cursorPorts b hs]
  simpa [cursorPorts, h859] using hb j


open HeadIdentifierProgram

/-- The existing native ID selector covers every free coordinate in the
chosen head, including coordinates with no incidences. -/
theorem chosen_free_head {n r Q : ℕ} (H : Finset (Fin n))
    (head : Fin n → MulticolorTypes.Word r Q) (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val ∈ chosenIds (predicate (headRows head)
      (lowBits (fun w => decide (w ∉ H))) (t.val * r + g.val)) n ↔
      ∃ hv : v ∉ H, head (⟨v, hv⟩ : {w : Fin n // w ∉ H}).val t = g := by
  rw [typed_chosen_mem]
  simp

/-- The reviewed source order equivalence names the same positions as the
actual head-size word and ID stream; it introduces no executable reindexing. -/
theorem freeOrder_eq_headOrder {n r : ℕ} (H : Finset (Fin n))
    (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (i : Fin (count p n)) :
    (BucketTupleProgram.Concrete.freeOrder H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs i).val.val = headOrder p n i := rfl

/-- Reindex the semantic head sum along the already proved source order.
Only the finite mathematical sum is transported; the machine still uses its
single bounded-width bit counter. -/
theorem counter_sum_eq_head {R : Type*} [AddCommMonoid R] {n r : ℕ}
    (H : Finset (Fin n)) (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
    (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (f : (Moments.Head head g → Bool) → R) :
    (∑ i ∈ Finset.range (2 ^ count p n), if hi : i < 2 ^ count p n then
      f ((BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
          (AttainedSignatures.assignmentEquiv (count p n) ⟨i, hi⟩)) else 0) =
      ∑ a : Moments.Head head g → Bool, f a := by
  rw [range_sum_eq_assignments (count p n) (fun bits =>
    f ((BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm bits))]
  exact (BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm.sum_comp f

/-- The concrete correction gate tests the selected original coordinates of
the typed head, using the same order as its assignment counter. -/
theorem candidate_correction_iff {n r : ℕ} (H E : Finset (Fin n))
    (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (candidate : {v : {v : Fin n // v ∉ H} // head v = g} → Bool) :
    LeafWeightProgram.good
      (List.ofFn (BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
      (HighIncidenceProgram.Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩))
      (List.replicate (count p n) true) = true ↔
      ∀ v : {v : {v : Fin n // v ∉ H} // head v = g},
        v.val.val ∈ E → candidate v = true := by
  let bits : Fin (count p n) → Bool :=
    BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate
  let order : Fin (count p n) ≃ {v : {v : Fin n // v ∉ H} // head v = g} :=
    BucketTupleProgram.Concrete.freeOrder H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs
  change LeafWeightProgram.good (List.ofFn bits)
    (HighIncidenceProgram.Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
      (LeafWeightProgram.supportBits ⟨E⟩))
    (List.replicate (count p n) true) = true ↔ _
  have hcorr := HeadRepresentativeSemantics.head_correction_iff p n E bits
  have hbits (i) : bits i = candidate (order i) := rfl
  have hval (i) : (order i).val.val = headOrder p n i := rfl
  constructor
  · intro h v hv
    have hc := hcorr.mp h
    obtain ⟨i, rfl⟩ := order.surjective v
    exact (hbits i).symm.trans (hc i (by simpa only [hval] using hv))
  · intro h
    apply hcorr.mpr
    intro i hi
    exact (hbits i).trans (h (order i) (by simpa only [hval] using hi))

/-- The paid ambient overlay realizes exactly the candidate substitution used
by restricted grouping, while retaining the fixed-high assignment. -/
theorem prepared_head_update {n r : ℕ} (H : Finset (Fin n))
    (high : H → Bool) (head : Fin n → Fin r) (g : Fin r) (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ _ : v ∉ H, head v = g)
    (reps : ∀ k, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) k → Bool)
    (candidate : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
    {steps : ℕ} (a b : HeadSumProgram.Data)
    (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
    (hbits : a.stacks 859 = List.ofFn
      (BucketTupleProgram.Concrete.freeAssignmentEquiv H
        (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs candidate))
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps))) :
    b.stacks 145 =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val)
          (Function.update reps g candidate))) := by
  have hh : (a.stacks 859).length =
      HighIncidenceProgram.Restriction.highCount (a.stacks 670) := by
    simp [hbits, hmask, HeadRepresentativeSemantics.headOrder_highCount, count]
  have hm : (a.stacks 670).length = (a.stacks 869).length := by
    simp [hmask, hbase]
  have hbits' := HighQueryAdapter.NativeOverlay.reset_frame a 859 (by decide)
  have hmask' := HighQueryAdapter.NativeOverlay.reset_frame a 670 (by decide)
  have hbase' := HighQueryAdapter.NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf, hc⟩ := HighQueryAdapter.NativeOverlay.command_eval
    (HighQueryAdapter.NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i
      HighQueryAdapter.NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits', hmask'] using hh)
    (by simpa only [hmask', hbase'] using hm)
  have heq := Eval.final_unique (859 : Fin 896) he
    ((HighQueryAdapter.NativeOverlay.reset_eval a).seq hc)
  rw [heq]
  let order := BucketTupleProgram.Concrete.freeOrder H
    (fun v : {v : Fin n // v ∉ H} => head v.val) g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs
  obtain ⟨current, hcurrent, hout⟩ := HeadSumAssembly.prepared_head_assignment a rf p n
    _ _ hbits hmask hbase
  have hm : (fun v : Fin n => p v.val) = (fun v => decide (v ∉ H ∧ head v = g)) := by
    funext v
    have hv := hs v
    simp only [chosenIds, List.mem_filter, List.mem_range, v.isLt, true_and,
      exists_prop] at hv
    exact Bool.eq_iff_iff.mpr (by simpa using hv)
  have hc : ∀ v (hv : v ∉ H) (hg : head v = g), current v = candidate ⟨⟨v, hv⟩, hg⟩ := by
    intro v hv hg
    let w : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g := ⟨⟨v, hv⟩, hg⟩
    have ho := order.apply_symm_apply w
    have hval : headOrder p n (order.symm w) = v := by
      have horder := freeOrder_eq_headOrder H
        (fun v : {v : Fin n // v ∉ H} => head v.val) g p hs (order.symm w)
      exact horder.symm.trans ((congrArg
        (fun x : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g =>
          x.val.val) ho).trans rfl)
    have hx := hcurrent (order.symm w)
    change current (headOrder p n (order.symm w)) = candidate (order (order.symm w)) at hx
    simpa only [hval, ho] using hx
  simp_rw [congrFun hm] at hout
  rw [← LeafAssignmentMergeProgram.merge_ofFn] at hout
  exact hout.trans (HeadRepresentativeSemantics.merge_candidate_ofFn H high head reps g
    candidate current hc)

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

/-- The actual full key and correction words admit exactly the intended
original-coordinate signature fiber. Every raw matrix row is retained. -/
theorem gate_source_iff {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H E : Finset (Fin n)) (node : Fin Q) (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val
          ((chosenIds pick n).get i))
    (candidate representative : Moments.Head
      (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool)
    (a : HeadSumProgram.Data) (hW : a.stacks 864 = W)
    (hbits : a.stacks 859 = List.ofFn (freeAssignmentEquiv H
      (fun v => head node v.val) g (chosenIds pick n)
      (chosenIds_bound pick n) (chosenIds_nodup pick n) hs candidate))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs representative))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true) :
    gateValue a (List.ofFn (fun j => List.ofFn (c j))) = true ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g candidate =
        HeadSourceLocality.freeLabel p ps P owner head H node g representative ∧
      ∀ v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
        v.val.val ∈ E → candidate v = true := by
  rw [gateValue, hW, hbits, hkey, hE, hH, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr
    (SignatureKeySource.key_eq_freeLabel p ps P owner head H node g
      (chosenIds pick n) (chosenIds_bound pick n) (chosenIds_nodup pick n) hs W c hc
      candidate representative)
    (candidate_correction_iff H E (fun v => head node v.val) g pick hs candidate)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
