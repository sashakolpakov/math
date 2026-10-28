import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

/-- The finite outer-search ABI is shared by local ternary matrices and
binary graph matrices. Only the current framed tuple and first witness persist. -/
def counterPorts : CounterForPrograms.Ports 16 48 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 40
  scratch := 41
  counter_ne_scratch := by decide

def setupPorts : Fin 4 ↪ Fin 48 := ⟨![46, 43, 40, 45], by decide⟩

def selection (candidate : Cmd 16 48) : Cmd 16 48 :=
  firstSuccess candidate 12 15 13 14 40 42 45

def core (candidate : Cmd 16 48) :=
  ExecCNFTupleEnumeration.program counterPorts (selection candidate)

def cleanup : Cmd 16 48 :=
  .seq (.call (StackRoutines.clearProgram 40 0 1))
    (.call (StackRoutines.clearProgram 42 0 1))

/-- Runtime preparation, all matrix attempts and final cleanup are fixed code.
The retained valid matrix stays at the concrete candidate's matrix port. -/
def command (candidate : Cmd 16 48) : Cmd 16 48 :=
  .seq (prepareSearch setupPorts) (.seq (.call (core candidate)) cleanup)


/-- Logical invariant of actual stored data. Only the counter and its scratch
are excluded from the boundary bound because their exact shapes are supplied
by the iterator. A saved tuple certifies the retained physical matrix. -/
structure Invariant (matrix : Fin 48) (Ready : State 16 48 → Prop)
    (Good : List Bool → Prop) (base : State 16 48) (B : ℕ) (a : State 16 48) : Prop where
  ready : Ready a
  bound : ∀ i, i ≠ 40 → i ≠ 41 → (a.stacks i).length ≤ B
  sound : a.stacks 42 ≠ [] → Good (a.stacks matrix)
  frame : ∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → a.stacks i = base.stacks i

theorem invariant_stable (matrix : Fin 48) (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (base : State 16 48) (B : ℕ) :
    CounterForPrograms.FrameStable counterPorts (fun _ => Invariant matrix Ready Good base B) := by
  intro _ a b hab ha
  have hf (i : Fin 48) (h40 : i ≠ 40) (h41 : i ≠ 41) : b.stacks i = a.stacks i :=
    (hab i h40 h41).symm
  refine ⟨hready a b ha.ready (fun i _ h40 h41 _ => hf i h40 h41), ?_, ?_, ?_⟩
  · intro i h40 h41
    rw [hf i h40 h41]
    exact ha.bound i h40 h41
  · intro hs
    rw [hf matrix hm40 hm41]
    exact ha.sound (by simpa only [hf 42 (by decide) (by decide)] using hs)
  · intro i hm h40 h41 h42
    exact (hf i h40 h41).trans (ha.frame i hm h40 h41 h42)

/-- Every actual first-success callback preserves its semantic witness and
polynomial boundary storage, and includes the complete checker's prefix cost. -/
theorem selection_runs (candidate : Cmd 16 48) (matrix : Fin 48)
    (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (hcopy : ∀ a, Ready a → a.stacks 45 = [])
    (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
    (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate d 2 → Ready a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
        (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks matrix)) ∧
        ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (a.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ C)
    (base a : State 16 48) (words : List (List Bool))
    (hw : words.map List.length = List.replicate d 2)
    (ha : Invariant matrix Ready Good base B a)
    (hc : a.stacks 40 = Encoding.encodeList id words) (hs : a.stacks 41 = []) :
    ∃ n out, n ≤ T + 7 * (B + C) + 10 ∧ Eval (selection candidate) n a out ∧
      out.stacks 40 = Encoding.encodeList id words ∧ out.stacks 41 = [] ∧
      Invariant matrix Ready Good base B out ∧
      ∀ k c, k ≤ n → Trace (compiled (selection candidate) 40 40) k
        (a.withPC (some (compiled (selection candidate) 40 40).entry)) c →
        ∀ i, (c.stacks i).length ≤ 56 * (B + C) + 10 := by
  have hab : ∀ i, (a.stacks i).length ≤ B := by
    intro i
    by_cases h40 : i = 40
    · subst i
      rw [hc, Enumerators.encoded_shape_length hw]
      simp only [List.sum_replicate, smul_eq_mul, List.length_replicate]
      omega
    by_cases h41 : i = 41
    · subst i
      simp [hs]
    · exact ha.bound i h40 h41
  let entry := (StructuredProgram.Atom.peek (42 : Fin 48) (13 : Fin 16) 12).eval a
  have hentry : entry.stacks = a.stacks := rfl
  have hentryReady : Ready entry := hready a entry ha.ready (fun _ _ _ _ _ => rfl)
  have hcheck : ∃ n b, n ≤ T ∧ Eval candidate n entry b ∧
      (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧ (b.regs 15 = true → Good (b.stacks matrix)) ∧
      ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
        (entry.withPC (some (compiled candidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ C :=
    hchecks words entry hw hentryReady hab hc
  have hrun : ∃ n out, n ≤ T + 7 * (B + C) + 10 ∧ Eval (selection candidate) n a out ∧
      ∀ k c, k ≤ n → Trace (compiled (selection candidate) 40 40) k
        (a.withPC (some (compiled (selection candidate) 40 40).entry)) c →
        ∀ i, (c.stacks i).length ≤ 56 * (B + C) + 10 := by
    by_cases hsaved : a.stacks 42 = []
    · obtain ⟨n, b, hn, he, hf, _, _, hp⟩ := hcheck
      have hb45 : b.stacks 45 = [] := (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready)
      have hp' : ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (entry.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ B + C := by
        intro k c hk ht i
        exact (hp k c hk ht i).trans (Nat.le_add_left _ _)
      obtain ⟨steps, out, heval, htime, hspace⟩ := firstSuccess_fresh_space candidate
        12 15 13 14 40 42 45 a b hsaved he hp' (by decide) (by decide) (by decide)
        (by decide) hb45
      refine ⟨steps, out, by omega, heval, ?_⟩
      intro k c hk ht i
      have h := hspace k c hk ht i
      omega
    · obtain ⟨out, he, _, hp⟩ := firstSuccess_saved_space candidate 12 15 13 14 40 42 45 a hsaved hab
      refine ⟨2, out, by omega, he, ?_⟩
      intro k c hk ht i
      have h := hp k c hk ht i
      omega
  obtain ⟨n, out, hn, he, hspace⟩ := hrun
  have hchecksFrame : a.stacks 42 = [] → ∃ n b, Eval candidate n entry b ∧
      b.stacks 42 = [] ∧ b.stacks 45 = [] ∧ (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ i, i ≠ matrix → b.stacks i = a.stacks i := by
    intro h42
    obtain ⟨n, b, _, he, hf, hb, _, _⟩ := hcheck
    exact ⟨n, b, he, (hf 42 (Ne.symm hm42)).trans h42,
      (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready), hb, hf⟩
  obtain ⟨hbound, hframe⟩ := firstSuccess_frame candidate 12 15 13 14 40 42 45 matrix a out
    (by decide) (by decide) (by decide) (by decide) hab hchecksFrame he
  have hsound := firstSuccess_matrix_sound candidate 12 15 13 14 40 42 45 matrix Good id a out
    (by decide) (by decide) (by decide) (by decide) hm42
    (fun h => ⟨a.stacks matrix, ha.sound h, rfl⟩)
    (by
      intro h42
      obtain ⟨n, b, _, he, hf, _, hgood, _⟩ := hcheck
      exact ⟨n, b, he, (hf 42 (Ne.symm hm42)).trans h42,
        (hf 45 (Ne.symm hm45)).trans (hcopy a ha.ready),
        fun h => ⟨b.stacks matrix, hgood h, rfl⟩⟩) he
  refine ⟨n, out, hn, he, (hframe 40 (Ne.symm hm40) (by decide)).trans hc,
    (hframe 41 (Ne.symm hm41) (by decide)).trans hs, ?_, hspace⟩
  refine ⟨hready a out ha.ready (fun i hm _ _ h42 => hframe i hm h42),
    fun i _ _ => hbound i, ?_, ?_⟩
  · intro h
    obtain ⟨word, hgood, hword⟩ := hsound h
    simpa only [hword, id_eq] using hgood
  · intro i hm h40 h41 h42
    exact (hframe i hm h42).trans (ha.frame i hm h40 h41 h42)


private theorem invariant_full_bound (matrix : Fin 48) (Ready : State 16 48 → Prop)
    (Good : List Bool → Prop) (base a : State 16 48) (d B : ℕ)
    (hcap : 6 * d + 1 ≤ B) (ha : Invariant matrix Ready Good base B a)
    (words : List (List Bool)) (hw : words.map List.length = List.replicate d 2)
    (hc : a.stacks 40 = Encoding.encodeList id words) (hs : a.stacks 41 = []) :
    ∀ i, (a.stacks i).length ≤ B := by
  intro i
  by_cases h40 : i = 40
  · subst i
    rw [hc, Enumerators.encoded_shape_length hw]
    simp only [List.sum_replicate, smul_eq_mul, List.length_replicate]
    omega
  by_cases h41 : i = 41
  · subst i
    simp [hs]
  · exact ha.bound i h40 h41

/-- A complete concrete candidate scan, including every failed attempt and
the final overflow reset. Target acceptance is later supplied by the existing
local-code and graph existence mathematics and the actual typed checker. -/
theorem core_runs (candidate : Cmd 16 48) (matrix : Fin 48)
    (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (hcopy : ∀ a, Ready a → a.stacks 45 = [])
    (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
    (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate d 2 → Ready a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
        (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks matrix)) ∧
        ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (a.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ C)
    (target : List (List Bool)) (htarget : target.map List.length = List.replicate d 2)
    (haccept : ∀ a, Ready a → (∀ i, (a.stacks i).length ≤ B) →
      a.stacks 40 = Encoding.encodeList id target →
      ∃ n b, Eval candidate n a b ∧ b.regs 15 = true)
    (base a : State 16 48) (ha : Invariant matrix Ready Good base B a)
    (hc : a.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]))
    (hs : a.stacks 41 = []) :
    ∃ n out, n ≤ 4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 ∧
      Trace (core candidate) n (a.withPC (some (core candidate).entry)) (out.withPC none) ∧
      Invariant matrix Ready Good base B out ∧ out.stacks 41 = [] ∧
      out.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) ∧
      out.stacks 42 ≠ [] ∧ Good (out.stacks matrix) ∧
      ∀ k c, k ≤ n → Trace (core candidate) k
        (a.withPC (some (core candidate).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4) := by
  let I := Invariant matrix Ready Good base B
  have stable := invariant_stable matrix hm40 hm41 Ready Good hready base B
  have spec : ExecCNFTupleEnumeration.BodySpec counterPorts (selection candidate)
      (List.replicate d 2) I (T + 7 * (B + C) + 10) := by
    intro words start hw hi hcurrent hscratch
    obtain ⟨n, out, hn, he, hc', hs', hi', _⟩ := selection_runs candidate matrix
      hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap hchecks
      base start words hw hi hcurrent hscratch
    exact ⟨n, out, hn, he, hc', hs', hi'⟩
  have hab := invariant_full_bound matrix Ready Good base a d B hcap ha
    (List.replicate d [false, false]) (by simp) hc hs
  obtain ⟨n, out, houtI, houtScratch, houtCounter, hn, htrace, hlog, hspace⟩ :=
    search_resources counterPorts candidate 12 15 13 14 42 45 d
      (T + 7 * (B + C) + 10) B (56 * (B + C) + 10) I stable spec
      (by
        intro words start finish nb hw hi _ hcurrent hscratch heval
        obtain ⟨m, finish', _, hr, hc', hs', hi', hp⟩ := selection_runs candidate matrix
          hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap hchecks
          base start words hw hi hcurrent hscratch
        have hnm := StreamResources.eval_steps_eq 40 42 heval hr
        have heq := heval.final_unique 40 hr
        subst finish'
        subst m
        exact ⟨invariant_full_bound matrix Ready Good base finish d B hcap hi' words hw hc' hs', hp⟩)
      a ha hab hc hs
  obtain ⟨loopSteps, _, hv⟩ := hlog
  have hmember : CounterPrograms.value target.flatten ∈ List.range' 0 (4 ^ d) := by
    have hlen : target.flatten.length = 2 * d := by
      rw [List.length_flatten, htarget, List.sum_replicate, smul_eq_mul]
      omega
    have hp : 2 ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
    have hlt := ExecCNFTupleOdometer.value_lt_power_length target.flatten
    rw [hlen, hp] at hlt
    simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hlt
  let J : State 16 48 → Prop := fun state => I state ∧ state.stacks 41 = []
  have hstart : J (ExecCNFTupleEnumeration.startResult counterPorts a) :=
    ⟨stable 0 a _ (fun _ _ _ => rfl) ha, hs⟩
  have hselected := search_reaches_success counterPorts candidate 12 15 13 14 42 45
    (by decide) (by decide) hv J hstart
    (by
      intro words start finish nb hw hcurrent heval hJ
      obtain ⟨m, finish', _, hr, _, hs', hi'⟩ := spec words start hw hJ.1 hcurrent hJ.2
      have heq := heval.final_unique 40 hr
      subst finish'
      exact ⟨hi', hs'⟩)
    (by
      intro words start hJ
      exact ⟨stable 0 start _ (ExecCNFTupleEnumeration.advanceResult_outside counterPorts start words)
        hJ.1, ExecCNFTupleEnumeration.advanceResult_scratch counterPorts start words⟩)
    target htarget hmember (by
      intro start finish nb hcurrent heval hJ
      by_cases hsaved : start.stacks 42 = []
      · let entry := (StructuredProgram.Atom.peek (42 : Fin 48) (13 : Fin 16) 12).eval start
        have heReady : Ready entry := hready start entry hJ.1.ready (fun _ _ _ _ _ => rfl)
        have heBound := invariant_full_bound matrix Ready Good base start d B hcap
          hJ.1 target htarget hcurrent hJ.2
        obtain ⟨m, b, hr, hyes⟩ := haccept entry heReady heBound hcurrent
        obtain ⟨m', b', _, hr', hf, _, _, _⟩ := hchecks target entry htarget heReady heBound hcurrent
        have heq := hr.final_unique 40 hr'
        subst b'
        have hb45 : b.stacks 45 = [] := (hf 45 (Ne.symm hm45)).trans (hcopy start hJ.1.ready)
        have hb42 : b.stacks 42 = [] := (hf 42 (Ne.symm hm42)).trans hsaved
        obtain ⟨saved, hsave, hword, _⟩ := firstSuccess_fresh_accept candidate 12 15 13 14 40 42 45
          start b hsaved hr hyes (by decide) (by decide) (by decide) (by decide) hb45 hb42
        have heq' := heval.final_unique 40 hsave
        subst finish
        rw [hword, hf 40 (Ne.symm hm40)]
        change start.stacks counterPorts.counter ≠ []
        rw [hcurrent]
        cases target <;> simp [Encoding.encodeList]
      · obtain ⟨saved, hsave, hframe⟩ := firstSuccess_saved candidate 12 15 13 14 40 42 45 start hsaved
        have heq := heval.final_unique 40 hsave
        subst finish
        simpa only [hframe] using hsaved)
  exact ⟨n, out, hn, htrace, houtI, houtScratch, houtCounter, hselected,
    houtI.sound hselected, hspace⟩


private theorem cleanup_eval (a : State 16 48) :
    ∃ out, Eval cleanup (2 * (a.stacks 40).length + 2 * (a.stacks 42).length + 6) a out ∧
      out.stacks = Function.update (Function.update a.stacks 40 []) 42 [] := by
  let b : State 16 48 := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 40 a.stacks⟩
  let out : State 16 48 := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 42 b.stacks⟩
  have h1 : Eval (.call (StackRoutines.clearProgram (s := 48) 40 (0 : Fin 16) 1))
      (2 * (a.stacks 40).length + 3) a b := .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  have h2 : Eval (.call (StackRoutines.clearProgram (s := 48) 42 (0 : Fin 16) 1))
      (2 * (b.stacks 42).length + 3) b out := .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  have hb : b.stacks 42 = a.stacks 42 := by simp [b, StackRoutines.clearStacks]
  refine ⟨out, ?_, rfl⟩
  have h := h1.seq h2
  rw [hb] at h
  convert h using 1
  · rfl
  · omega

def timeBudget (d B T C : ℕ) : ℕ :=
  4 ^ d * (T + 7 * (B + C) + 10 + 42 * d + 12) + 3 + 15 * d + 4 * B + 17

def spaceBudget (d B C : ℕ) : ℕ :=
  48 * B + 15 * d + max (56 * (B + C) + 10) (48 * B + 7 * (6 * d + 1) + 4) + 4 * B + 17

/-- Setup, exhaustive first-success search, readout retention and cleanup form
one actual run. All candidate services in this intermediate lemma are explicit
fixed commands, instantiated below by the native local and graph checkers. -/
theorem command_runs (candidate : Cmd 16 48) (matrix : Fin 48)
    (hm40 : matrix ≠ 40) (hm41 : matrix ≠ 41) (hm42 : matrix ≠ 42) (hm45 : matrix ≠ 45)
    (Ready : State 16 48 → Prop) (Good : List Bool → Prop)
    (hready : ∀ a b, Ready a →
      (∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → b.stacks i = a.stacks i) → Ready b)
    (hcopy : ∀ a, Ready a → a.stacks 45 = [])
    (d B T C : ℕ) (hcap : 6 * d + 1 ≤ B)
    (hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate d 2 → Ready a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ T ∧ Eval candidate n a b ∧
        (∀ i, i ≠ matrix → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks matrix)) ∧
        ∀ k c, k ≤ n → Trace (compiled candidate 40 42) k
          (a.withPC (some (compiled candidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ C)
    (target : List (List Bool)) (htarget : target.map List.length = List.replicate d 2)
    (haccept : ∀ a, Ready a → (∀ i, (a.stacks i).length ≤ B) →
      a.stacks 40 = Encoding.encodeList id target →
      ∃ n b, Eval candidate n a b ∧ b.regs 15 = true)
    (a : State 16 48) (ha : Ready a) (hab : ∀ i, (a.stacks i).length ≤ B)
    (hdim : (a.stacks 46).length = d)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = [])
    (h43 : a.stacks 43 = []) :
    ∃ n out, n ≤ timeBudget d B T C ∧ Eval (command candidate) n a out ∧
      Good (out.stacks matrix) ∧ Ready out ∧
      (∀ i, i ≠ matrix → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      ∀ k c, k ≤ n → Trace (compiled (command candidate) 46 matrix) k
        (a.withPC (some (compiled (command candidate) 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
  obtain ⟨prepared, hp, hpstacks⟩ := prepareSearch_eval setupPorts a h43 h40 (hcopy a ha)
  have hptime : 15 * (a.stacks (setupPorts 0)).length + 11 = 15 * d + 11 := by
    simp [setupPorts, hdim]
  rw [hptime] at hp
  have hprepared : prepared.stacks = Function.update a.stacks 40
      (Encoding.encodeList id (List.replicate d [false, false])) := by
    rw [show setupPorts 2 = 40 by decide, show setupPorts 0 = 46 by decide,
      hdim] at hpstacks
    exact hpstacks
  have hf (i : Fin 48) (hi : i ≠ 40) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hI : Invariant matrix Ready Good a B prepared := by
    refine ⟨hready a prepared ha (fun i _ hi _ _ => hf i hi), ?_, ?_, ?_⟩
    · intro i hi _
      rw [hf i hi]
      exact hab i
    · intro hn
      exact (hn ((hf 42 (by decide)).trans h42)).elim
    · intro i _ hi _ _
      exact hf i hi
  have hc : prepared.stacks 40 = Encoding.encodeList id (List.replicate d [false, false]) := by
    rw [hprepared, Function.update_self]
  have hs : prepared.stacks 41 = [] := (hf 41 (by decide)).trans h41
  obtain ⟨nc, middle, hnc, hcore, hmiddle, hms, hmc, _, hgood, hcoreSpace⟩ :=
    core_runs candidate matrix hm40 hm41 hm42 hm45 Ready Good hready hcopy d B T C hcap
      hchecks target htarget haccept a prepared hI hc hs
  have hmiddleBound := invariant_full_bound matrix Ready Good a middle d B hcap hmiddle
    (List.replicate d [false, false]) (by simp) hmc hms
  obtain ⟨out, hclean, hout⟩ := cleanup_eval middle
  have houtFrame (i : Fin 48) (hi40 : i ≠ 40) (hi42 : i ≠ 42) :
      out.stacks i = middle.stacks i := by
    rw [hout, Function.update_of_ne hi42, Function.update_of_ne hi40]
  have houtBound : ∀ i, (out.stacks i).length ≤ B := by
    intro i
    by_cases hi40 : i = 40
    · subst i
      simp [hout]
    by_cases hi42 : i = 42
    · subst i
      simp [hout]
    · rw [houtFrame i hi40 hi42]
      exact hmiddleBound i
  have hcall : Eval (.call (core candidate)) nc prepared middle := .call _ hcore
  have hprepSpace : ∀ k c, k ≤ 15 * d + 11 →
      Trace (compiled (prepareSearch setupPorts) 46 matrix) k
        (a.withPC (some (compiled (prepareSearch setupPorts) 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := hab i
    unfold spaceBudget
    omega
  have hcallSpace : ∀ k c, k ≤ nc → Trace (compiled (.call (core candidate)) 46 matrix) k
      (prepared.withPC (some (compiled (.call (core candidate)) 46 matrix).entry)) c →
      ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    have h := StructuredSpace.call_stack_bound (core candidate)
      (compiled (.call (core candidate)) 46 matrix) (siteAddress (.call (core candidate)))
      (exitAddress (.call (core candidate)))
      (fun pc => compiled_site (.call (core candidate)) 46 matrix pc) hcore hcoreSpace
    intro k c hk ht i
    have hb := h k c hk ht i
    unfold spaceBudget
    omega
  have hcleanSpace : ∀ k c, k ≤ 2 * (middle.stacks 40).length + 2 * (middle.stacks 42).length + 6 →
      Trace (compiled cleanup 46 matrix) k
        (middle.withPC (some (compiled cleanup 46 matrix).entry)) c →
        ∀ i, (c.stacks i).length ≤ spaceBudget d B C := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (middle.stacks i).length + k at hg
    have hi := hmiddleBound i
    have h40b := hmiddleBound 40
    have h42b := hmiddleBound 42
    unfold spaceBudget
    omega
  refine ⟨(15 * d + 11) + (nc + (2 * (middle.stacks 40).length +
    2 * (middle.stacks 42).length + 6)), out, ?_, hp.seq (hcall.seq hclean), ?_, ?_, ?_, houtBound, ?_⟩
  · have h40b := hmiddleBound 40
    have h42b := hmiddleBound 42
    unfold timeBudget
    omega
  · rwa [houtFrame matrix hm40 hm42]
  · exact hready middle out hmiddle.ready (fun i _ hi40 _ hi42 => houtFrame i hi40 hi42)
  · intro i him
    by_cases hi40 : i = 40
    · subst i
      simp [hout, h40]
    by_cases hi42 : i = 42
    · subst i
      simp [hout, h42]
    rw [houtFrame i hi40 hi42]
    by_cases hi41 : i = 41
    · subst i
      exact hms.trans h41.symm
    · exact hmiddle.frame i him hi40 hi41 hi42
  · have htail := StructuredSpace.sequence_stack_bound hcall hclean 46 matrix
      hcallSpace hcleanSpace (compiled (.seq (.call (core candidate)) cleanup) 46 matrix)
      (siteAddress (.seq (.call (core candidate)) cleanup))
      (exitAddress (.seq (.call (core candidate)) cleanup)) (compiled_site _ 46 matrix)
    exact StructuredSpace.sequence_stack_bound hp (hcall.seq hclean) 46 matrix hprepSpace htail
      (compiled (command candidate) 46 matrix) (siteAddress (command candidate))
      (exitAddress (command candidate)) (compiled_site _ 46 matrix)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

def localSearch : Cmd 16 48 := command localMatrixCandidate

def graphSearch : Cmd 16 48 := command graphMatrixCandidate

def boundary (A dimension : ℕ) : ℕ := A + 6 * dimension + 1

def localTime (A t D d : ℕ) : ℕ :=
  timeBudget (t * D) (boundary A (t * D))
    (candidateBudget (boundary A (t * D)) (t * D) D (callbackBudget t D d) (localStreamBudget t D d))
    (candidateSpace (boundary A (t * D)) (t * D) D (callbackBudget t D d))

def localSpace (A t D d : ℕ) : ℕ :=
  spaceBudget (t * D) (boundary A (t * D))
    (candidateSpace (boundary A (t * D)) (t * D) D (callbackBudget t D d))

def graphTime (A D r qlen Dlen : ℕ) : ℕ :=
  timeBudget (D * r) (boundary A (D * r))
    (candidateBudget (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen)
      (graphStreamBudget D r qlen Dlen))
    (candidateSpace (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen))

def graphSpace (A D r qlen Dlen : ℕ) : ℕ :=
  spaceBudget (D * r) (boundary A (D * r))
    (candidateSpace (boundary A (D * r)) (D * r) r (graphCallbackBudget D r qlen Dlen))

private theorem ternary_target_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (xs : List (Bool × Bool)) (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords Q) :
    xs.any (CodeCandidates.invalidDigit true) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : CodeCandidates.digitBits x ∈ CodeCandidates.matrixWords Q :=
    h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [CodeCandidates.ternary_digit_complete x
    (Q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) hi.symm]

private theorem binary_target_valid {D r : ℕ} (Q : Fin D → Cayley.Cube r)
    (xs : List (Bool × Bool)) (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords Q) :
    xs.any (CodeCandidates.invalidDigit false) = false := by
  apply List.any_eq_false.mpr
  intro x hx
  have hm : CodeCandidates.digitBits x ∈ CodeCandidates.matrixWords Q :=
    h ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  simp [CodeCandidates.binary_digit_complete x
    (Q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) hi.symm]

/-- Actual exhaustive ternary code search with polynomial storage on the same
run. The pure existence premise is discharged for the supplied parameters
below; no evaluator, layout or successful candidate is supplied to the code. -/
theorem local_search_runs (t D d A : ℕ)
    (hexists : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d)
    (a : State 16 48) (ha : LocalMatrixReady t D d a)
    (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (t * D) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin t → Fin D → SparseCode.F3), n ≤ localTime A t D d ∧
      Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧ SparseCode.HasDistance Q d ∧
      LocalMatrixReady t D d out ∧ (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A (t * D)) ∧
      ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
        (a.withPC (some (compiled localSearch 46 18).entry)) c →
        ∀ i, (c.stacks i).length ≤ localSpace A t D d := by
  let B := boundary A (t * D)
  let Good : List Bool → Prop := fun word => ∃ Q : Fin t → Fin D → SparseCode.F3,
    word = matrixFrames Q ∧ SparseCode.HasDistance Q d
  have hB : 6 * (t * D) + 1 ≤ B := by dsimp [B, boundary]; omega
  have hcap : 5 * (t * D) ≤ B := by omega
  have hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate (t * D) 2 → (LocalMatrixReady t D d) a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ candidateBudget B (t * D) D (callbackBudget t D d) (localStreamBudget t D d) ∧ Eval localMatrixCandidate n a b ∧
        (∀ i, i ≠ 18 → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks 18)) ∧
        ∀ k c, k ≤ n → Trace (compiled localMatrixCandidate 40 42) k
          (a.withPC (some (compiled localMatrixCandidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ candidateSpace B (t * D) D (callbackBudget t D d) := by
    intro words start hw hready hb hc
    obtain ⟨n, out, hn, he, _, hf, hbound, hsound, hspace⟩ :=
      local_matrix_candidate_runs t D d start B hb hcap hready words hw hc
    exact ⟨n, out, hn, he, hf, hbound, hsound, hspace⟩
  obtain ⟨targetQ, htargetQ⟩ := hexists
  have hwidth : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  have hshape : (CodeCandidates.matrixWords targetQ).map List.length = List.replicate (t * D) 2 := by
    simpa only [hwidth] using CodeCandidates.matrixWords_shape targetQ
  have htarget : ∀ start, LocalMatrixReady t D d start →
      (∀ i, (start.stacks i).length ≤ B) →
      start.stacks 40 = Encoding.encodeList id (CodeCandidates.matrixWords targetQ) →
      ∃ n out, Eval localMatrixCandidate n start out ∧ out.regs 15 = true := by
    intro start hready hb hc
    obtain ⟨xs, _, hfields⟩ := CodeCandidates.pairs_of_shape (CodeCandidates.matrixWords targetQ)
      (t * D) hshape
    have hcurrent : start.stacks 40 = CodeCandidates.tupleBits xs := by rw [hc, tupleBits_eq, hfields]
    obtain ⟨n, out, _, he, hyes, _, _⟩ := local_matrix_candidate_valid targetQ d xs hfields
      (ternary_target_valid targetQ xs hfields) start B hb hready.work hready.rows
      hready.distance hready.dimension hready.payload hready.scratch hready.counter hready.latch
      hready.counterScratch hready.copy hcurrent hready.outerInput hready.outerPayload hready.outerScratch
    exact ⟨n, out, he, hyes.mpr htargetQ⟩
  obtain ⟨n, out, hn, he, hgood, hready, hframe, hbound, hspace⟩ := command_runs
    localMatrixCandidate 18 (by decide) (by decide) (by decide) (by decide)
    (LocalMatrixReady t D d) Good (fun _ _ h hf => h.frame hf) (fun _ h => h.outerScratch)
    (t * D) B _ _ hB hchecks (CodeCandidates.matrixWords targetQ) hshape htarget a ha
    (fun i => (hab i).trans (by dsimp [B, boundary]; omega))
    (by simp [hdim]) h40 h41 h42 ha.outerInput
  obtain ⟨Q, hmatrix, hQ⟩ := hgood
  exact ⟨n, out, Q, hn, he, hmatrix, hQ, hready, hframe, hbound, hspace⟩

/-- Actual exhaustive graph-code search has the same physical output and
same-run resource guarantees, including invalid two-bit field digits. -/
theorem graph_search_runs (D r q A : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (hexists : ∃ Q : Fin D → Cayley.Cube r, WalshExistence.Good q Q)
    (a : State 16 48) (ha : GraphMatrixReady D r qbits Dbits a)
    (hab : ∀ i, (a.stacks i).length ≤ A) (hdim : a.stacks 46 = List.replicate (D * r) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin D → Cayley.Cube r), n ≤ graphTime A D r qbits.length Dbits.length ∧
      Eval graphSearch n a out ∧ out.stacks 29 = matrixFrames Q ∧ WalshExistence.Good q Q ∧
      GraphMatrixReady D r qbits Dbits out ∧ (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A (D * r)) ∧
      ∀ k c, k ≤ n → Trace (compiled graphSearch 46 29) k
        (a.withPC (some (compiled graphSearch 46 29).entry)) c →
        ∀ i, (c.stacks i).length ≤ graphSpace A D r qbits.length Dbits.length := by
  let B := boundary A (D * r)
  let Good : List Bool → Prop := fun word => ∃ Q : Fin D → Cayley.Cube r,
    word = matrixFrames Q ∧ WalshExistence.Good q Q
  have hB : 6 * (D * r) + 1 ≤ B := by dsimp [B, boundary]; omega
  have hcap : 5 * (D * r) ≤ B := by omega
  have hchecks : ∀ (words : List (List Bool)) (a : State 16 48),
      words.map List.length = List.replicate (D * r) 2 → (GraphMatrixReady D r qbits Dbits) a →
      (∀ i, (a.stacks i).length ≤ B) → a.stacks 40 = Encoding.encodeList id words →
      ∃ n b, n ≤ candidateBudget B (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
          (graphStreamBudget D r qbits.length Dbits.length) ∧ Eval graphMatrixCandidate n a b ∧
        (∀ i, i ≠ 29 → b.stacks i = a.stacks i) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        (b.regs 15 = true → Good (b.stacks 29)) ∧
        ∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
          (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ candidateSpace B (D * r) r (graphCallbackBudget D r qbits.length Dbits.length) := by
    intro words start hw hready hb hc
    obtain ⟨n, out, hn, he, _, hf, hbound, hsound, hspace⟩ :=
      graph_matrix_candidate_runs D r q qbits Dbits hqv hDv start B hb hcap hready words hw hc
    exact ⟨n, out, hn, he, hf, hbound, hsound, hspace⟩
  obtain ⟨targetQ, htargetQ⟩ := hexists
  have hwidth : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  have hshape : (CodeCandidates.matrixWords targetQ).map List.length = List.replicate (D * r) 2 := by
    simpa only [hwidth] using CodeCandidates.matrixWords_shape targetQ
  have htarget : ∀ start, GraphMatrixReady D r qbits Dbits start →
      (∀ i, (start.stacks i).length ≤ B) →
      start.stacks 40 = Encoding.encodeList id (CodeCandidates.matrixWords targetQ) →
      ∃ n out, Eval graphMatrixCandidate n start out ∧ out.regs 15 = true := by
    intro start hready hb hc
    obtain ⟨xs, _, hfields⟩ := CodeCandidates.pairs_of_shape (CodeCandidates.matrixWords targetQ)
      (D * r) hshape
    have hcurrent : start.stacks 40 = CodeCandidates.tupleBits xs := by rw [hc, tupleBits_eq, hfields]
    obtain ⟨n, out, _, he, hyes, _, _⟩ := graph_matrix_candidate_valid targetQ q qbits Dbits hqv hDv
      xs hfields (binary_target_valid targetQ xs hfields) start B hb hready.work hready.degree
      hready.quotient hready.degreeBits hready.dimension hready.payload hready.scratch hready.counter
      hready.latch hready.counterScratch hready.copy hcurrent hready.outerInput hready.outerPayload
      hready.outerScratch
    exact ⟨n, out, he, hyes.mpr htargetQ⟩
  obtain ⟨n, out, hn, he, hgood, hready, hframe, hbound, hspace⟩ := command_runs
    graphMatrixCandidate 29 (by decide) (by decide) (by decide) (by decide)
    (GraphMatrixReady D r qbits Dbits) Good (fun _ _ h hf => h.frame hf) (fun _ h => h.outerScratch)
    (D * r) B _ _ hB hchecks (CodeCandidates.matrixWords targetQ) hshape htarget a ha
    (fun i => (hab i).trans (by dsimp [B, boundary]; omega))
    (by simp [hdim]) h40 h41 h42 ha.outerInput
  obtain ⟨Q, hmatrix, hQ⟩ := hgood
  exact ⟨n, out, Q, hn, he, hmatrix, hQ, hready, hframe, hbound, hspace⟩


/-- Supplied sparse-code parameters discharge pure local-code existence; the
machine still searches and checks its own actual output matrix. -/
theorem local_parameters_runs {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : State 16 48)
    (ha : LocalMatrixReady (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) a)
    (hab : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      n ≤ localTime A (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      LocalMatrixReady (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) out ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
        (a.withPC (some (compiled localSearch 46 18).entry)) c →
        ∀ i, (c.stacks i).length ≤ localSpace A (SparseCode.localRows m occurrence)
          (SparseCode.degree m occurrence)
          (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) :=
  local_search_runs _ _ _ A (SparseCodeProgram.candidates_exist hm hocc).2
    a ha hab hdim h40 h41 h42

/-- Graph existence is likewise discharged from the supplied arithmetic
parameters, including dimension zero. The actual search order remains binary. -/
theorem graph_parameters_runs {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = SparseCode.gapDenom m occurrence)
    (hDv : BinaryArithmetic.toNat Dbits = SparseCode.degree m occurrence)
    (a : State 16 48)
    (ha : GraphMatrixReady (SparseCode.degree m occurrence) (SparseCode.dimension m occurrence) qbits Dbits a)
    (hab : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
      n ≤ graphTime A (SparseCode.degree m occurrence) (SparseCode.dimension m occurrence)
        qbits.length Dbits.length ∧
      Eval graphSearch n a out ∧ out.stacks 29 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
      GraphMatrixReady (SparseCode.degree m occurrence) (SparseCode.dimension m occurrence) qbits Dbits out ∧
      (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
      ∀ k c, k ≤ n → Trace (compiled graphSearch 46 29) k
        (a.withPC (some (compiled graphSearch 46 29).entry)) c →
        ∀ i, (c.stacks i).length ≤ graphSpace A (SparseCode.degree m occurrence)
          (SparseCode.dimension m occurrence) qbits.length Dbits.length :=
  graph_search_runs _ _ _ A qbits Dbits hqv hDv (SparseCodeProgram.candidates_exist hm hocc).1
    a ha hab hdim h40 h41 h42


/-- Fixed injection into the original leaf bank; high metadata, selected rows,
and the leaf controller's upper Boolean registers remain caller-owned. -/
def leafRegisters : Fin 16 → Fin 40 := Fin.castAdd 24

def leafStacks : Fin 48 → Fin 896 := Fin.castAdd 848

def leafCall (routine : Cmd 16 48) (output : Fin 48) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)

/-- The concrete search's whole matrix readback and uniform storage survive
its actual embedding into the shared leaf ABI. The final callee halt is paid. -/
theorem leaf_call_resources (routine : Cmd 16 48) (output : Fin 48)
    (a : State 40 896) (small : State 16 48) {n A B : ℕ}
    (he : Eval routine n (projectState leafRegisters leafStacks a) small)
    (hframe : ∀ i, i ≠ output → small.stacks i = (projectState leafRegisters leafStacks a).stacks i)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ n → Trace (compiled routine 46 output) k
      ((projectState leafRegisters leafStacks a).withPC (some (compiled routine 46 output).entry)) c →
      ∀ i, (c.stacks i).length ≤ B) :
    ∃ out, Eval (leafCall routine output) (n + 1) a out ∧
      out.stacks (leafStacks output) = small.stacks output ∧
      (∀ i, i ≠ leafStacks output → out.stacks i = a.stacks i) ∧
      (∀ i, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ k c, k ≤ n + 1 → Trace (compiled (leafCall routine output) (leafStacks 46) (leafStacks output)) k
        (a.withPC (some (compiled (leafCall routine output) (leafStacks 46) (leafStacks output)).entry)) c →
        ∀ i, (c.stacks i).length ≤ max B A := by
  let out := embedState leafRegisters leafStacks a small
  have ht := compiled_halt_trace he 46 output
  have hs := StructuredSpace.compiled_halt_stack_bound he 46 output hspace
  have hc := eval_call_from_state (compiled routine 46 output) leafRegisters leafStacks a
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht
  have hinitial : ProgramLinking.embedCfg leafRegisters leafStacks id none
      (a.withPC (none : Option (Fin (size routine + 1))))
      ((projectState leafRegisters leafStacks a).withPC (some (compiled routine 46 output).entry)) =
      a.withPC (some (compiled routine 46 output).entry) := by
    change (embedState leafRegisters leafStacks a (projectState leafRegisters leafStacks a)).withPC _ = _
    rw [embedState_project leafRegisters leafStacks a (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)]
    rfl
  have hlift := ProgramLinking.liftProgram_trace (compiled routine 46 output) leafRegisters leafStacks
    (a.withPC none) (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht
  rw [hinitial] at hlift
  have hlift' : Trace (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)
      (n + 1) (a.withPC (some (compiled routine 46 output).entry)) (out.withPC none) := by
    simpa [out, embedState, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC] using hlift
  have hliftspace := StructuredSpace.liftProgram_stack_bound
    (compiled routine 46 output) leafRegisters leafStacks (a.withPC none)
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht hs ha
  rw [hinitial] at hliftspace
  refine ⟨out, hc, embedState_stack leafRegisters leafStacks a small (Fin.castAdd_injective _ _) output,
    ?_, ?_, ?_⟩
  · intro i hi
    by_cases hport : ∃ j, leafStacks j = i
    · obtain ⟨j, rfl⟩ := hport
      have hj : j ≠ output := by intro h; exact hi (congrArg leafStacks h)
      exact (embedState_stack leafRegisters leafStacks a small (Fin.castAdd_injective _ _) j).trans
        (hframe j hj)
    · exact embedState_stack_frame leafRegisters leafStacks a small i hport
  · intro i hi
    apply embedState_register_frame leafRegisters leafStacks a small i
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  · exact StructuredSpace.call_stack_bound
      (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)
      (compiled (leafCall routine output) (leafStacks 46) (leafStacks output))
      (siteAddress (leafCall routine output)) (exitAddress (leafCall routine output))
      (compiled_site (leafCall routine output) (leafStacks 46) (leafStacks output)) hlift' hliftspace


/-- High leaf metadata is untouched at every prefix of the actual lifted
search table, including prefixes deep inside either nested checker. -/
theorem leaf_prefix_frame {l steps prefixSteps : ℕ}
    (p : Program 16 48 l) (frame : Cfg 40 896 l) {a b : Cfg 16 48 l}
    (tr : Trace p steps a b) {intermediate : Cfg 40 896 l}
    (hp : prefixSteps ≤ steps)
    (ht : Trace (ProgramLinking.liftProgram p leafRegisters leafStacks) prefixSteps
      (ProgramLinking.embedCfg leafRegisters leafStacks id none frame a) intermediate)
    (i : Fin 896) (hi : 48 ≤ i.val) : intermediate.stacks i = frame.stacks i := by
  apply StreamResources.relocate_trace_stack_frame p _ leafRegisters leafStacks id none frame
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) (fun _ => rfl) tr hp ht i
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
