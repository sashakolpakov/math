import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

/-! Every source prefix of the actual pruned pair traversal. The two masks
carry the DFS phases; the resource invariant counts all caller stacks as well
as the four controller stacks. Callback time never contributes to the space
bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace

open BitProgram StructuredCalls DifferencePairsProgram

variable {r s : ℕ}

private theorem short_prefix (p : Ports r s) {c : Cmd r s} {d : State r s}
    {B t : ℕ} (hb : ∀ i, (d.stacks i).length ≤ B) (ht : t ≤ 13) :
    ∀ q e, q ≤ t →
      Trace (compiled c (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled c (p.stack 0) (p.stack 2)).entry)) e →
      ∀ i, (e.stacks i).length ≤ s * B + 13 := by
  intro q e hq he i
  exact StructuredSpace.local_stack_bound (compiled c (p.stack 0) (p.stack 2))
    (steps := 13) (StreamResources.dataBits_le_mul _ hb) q e (hq.trans ht) he i

private theorem cursor_bound (p : Ports r s) {N J B n j : ℕ}
    {pre : List (Option Bool)} {down : Bool} {a d : State r s}
    (hN : N ≤ B) (hJ : J ≤ B) (hn : n + pre.length = N)
    (hj : j + pre.countP Option.isSome = J) (hc : Cursor p n j pre down d)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hf : ∀ i, (∀ k, i ≠ p.stack k) → d.stacks i = a.stacks i) :
    ∀ i, (d.stacks i).length ≤ B := by
  intro i
  by_cases h : ∃ k, i = p.stack k
  · obtain ⟨k, rfl⟩ := h
    fin_cases k
    · change (d.stacks (p.stack 0)).length ≤ B
      rw [hc.depth, List.length_replicate]; omega
    · change (d.stacks (p.stack 1)).length ≤ B
      rw [hc.budget, List.length_replicate]; omega
    · change (d.stacks (p.stack 2)).length ≤ B
      rw [hc.outer, List.length_reverse, List.length_map]; omega
    · change (d.stacks (p.stack 3)).length ≤ B
      rw [hc.inner, List.length_reverse, List.length_map]; omega
  · rw [hf i (by simpa using h)]
    exact ha i

/-- The callback branch has three control instructions before the callback and
two register updates after it. The callback's own uniform bound is retained. -/
theorem callback_prefix (p : Ports r s) (callback : Cmd r s)
    {d e : State r s} {t B D : ℕ}
    (hd : d.regs (p.register 0) = true) (hn : d.stacks (p.stack 0) = [])
    (hb : ∀ i, (d.stacks i).length ≤ B)
    (he : ∀ i, (e.stacks i).length ≤ B)
    (hc : Eval callback t (popped p 0 2 d) e)
    (hp : ∀ q z, q ≤ t →
      Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 d).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ D) :
    ∀ q z, q ≤ t + 5 →
      Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  let tail : Cmd r s := atoms [.set (p.register 0) false, .set (p.register 1) true]
  have htail : Eval tail 2 e (returned p e) := atoms_eval _ e
  have ht := short_prefix p (c := tail) he (show 2 ≤ 13 by omega)
  have ht' : ∀ q z, q ≤ 2 →
      Trace (compiled tail (p.stack 0) (p.stack 2)) q
        (e.withPC (some (compiled tail (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (ht q z hq hz i).trans (Nat.le_max_right _ _)
  have hp' : ∀ q z, q ≤ t →
      Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 d).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (hp q z hq hz i).trans (Nat.le_max_left _ _)
  have hseq := StructuredSpace.sequence_stack_bound hc htail (p.stack 0) (p.stack 2)
    hp' ht' (compiled (.seq callback tail) (p.stack 0) (p.stack 2))
    (siteAddress (.seq callback tail)) (exitAddress (.seq callback tail))
    (compiled_site _ (p.stack 0) (p.stack 2))
  have hfalse : (popped p 0 2 d).regs (p.register 3) = false := by
    simp [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hn]
  have hcond := StructuredSpace.conditional_false_stack_bound
    (yes := enter p false false) hfalse (hc.seq htail) (p.stack 0) (p.stack 2) hseq
    (compiled (.ite (p.register 3) (enter p false false) (.seq callback tail))
      (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  have hpop : Eval (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
      1 d (popped p 0 2 d) := atoms_eval _ d
  have hpop' : ∀ q z, q ≤ 1 →
      Trace (compiled (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
        (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled
          (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
          (p.stack 0) (p.stack 2)).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    intro q z hq hz i
    exact (short_prefix p hb (show 1 ≤ 13 by omega) q z hq hz i).trans
      (Nat.le_max_right _ _)
  have hdesc := StructuredSpace.sequence_stack_bound hpop
    (Eval.ite_false hfalse (hc.seq htail)) (p.stack 0) (p.stack 2) hpop' hcond
    (compiled (descend p callback) (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  have h := StructuredSpace.conditional_true_stack_bound (no := backtrack p) hd
    (hpop.seq (Eval.ite_false hfalse (hc.seq htail))) (p.stack 0) (p.stack 2) hdesc
    (compiled (body p callback) (p.stack 0) (p.stack 2))
    (siteAddress _) (exitAddress _) (compiled_site _ (p.stack 0) (p.stack 2))
  intro q z hq hz
  exact h q z (by omega) hz

/-- One real DFS body step preserves the bounded controller geometry and all
persistent stack bounds. The only unbounded-time branch is split around its
actual callback. -/
theorem body_resources (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I) (hN : N ≤ B) (hJ : J ≤ B)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {n j : ℕ} {pre : List (Option Bool)} {down : Bool} {d : State r s}
    (hc : Cursor p n (j + 1) pre down d) (hn : n + pre.length = N)
    (hj : (j + 1) + pre.countP Option.isSome = J)
    (hb : ∀ i, (d.stacks i).length ≤ B) (hI : I d) :
    ∃ t e, Eval (body p callback) t d e ∧ I e ∧
      (∀ i, (e.stacks i).length ≤ B) ∧
      (e.regs (p.register 1) = true →
        ∃ n j pre down, Cursor p n (j + 1) pre down e ∧
          n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) ∧
      ∀ q z, q ≤ t → Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
        (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have short {e : State r s} {t n' j' : ℕ} {pre' : List (Option Bool)} {down' : Bool}
      (heval : Eval (body p callback) t d e) (ht : t ≤ 13)
      (hc' : Cursor p n' (j' + 1) pre' down' e)
      (hn' : n' + pre'.length = N)
      (hj' : (j' + 1) + pre'.countP Option.isSome = J)
      (hf : ∀ i, (∀ k, i ≠ p.stack k) → e.stacks i = d.stacks i) :
      ∃ t e, Eval (body p callback) t d e ∧ I e ∧
        (∀ i, (e.stacks i).length ≤ B) ∧
        (e.regs (p.register 1) = true →
          ∃ n j pre down, Cursor p n (j + 1) pre down e ∧
            n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) ∧
        ∀ q z, q ≤ t → Trace (compiled (body p callback) (p.stack 0) (p.stack 2)) q
          (d.withPC (some (compiled (body p callback) (p.stack 0) (p.stack 2)).entry)) z →
          ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
    refine ⟨t, e, heval, spec.stable d e hf hI, cursor_bound p hN hJ hn' hj' hc' hb hf,
      (fun _ => ⟨n', j', pre', down', hc', hn', hj'⟩), ?_⟩
    intro q z hq hz i
    exact (short_prefix p hb ht q z hq hz i).trans (Nat.le_max_right _ _)
  cases down with
  | true =>
      cases n with
      | zero =>
          obtain ⟨t, e, _, he, hf, _, hIe⟩ := spec.run j pre d (by omega) hc hI
          obtain ⟨heB, heD⟩ := hcallback j pre d e t (by simpa using hn) hj hc hI hb he
          have hr : Cursor p 0 (j + 1) pre false (returned p e) :=
            ⟨(hf 0).trans hc.depth, (hf 1).trans hc.budget, (hf 2).trans hc.outer,
              (hf 3).trans hc.inner, returned_descending p e, returned_active p e⟩
          refine ⟨t + 5, returned p e,
            body_callback p callback d e hc.descending (by simpa using hc.depth) t he,
            spec.stable e (returned p e) (by intros; rfl) hIe,
            heB, (fun _ => ⟨0, j, pre, false, hr, hn, hj⟩), ?_⟩
          exact callback_prefix p callback hc.descending (by simpa using hc.depth) hb heB he heD
      | succ n =>
          apply short (body_descend p callback d hc.descending true (List.replicate n true)
            (by simpa [List.replicate_succ] using hc.depth)) (by omega)
            (cursor_descend p n (j + 1) pre d hc)
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
          · simpa using hj
          · intro i hi
            simp [descended, entered_frame _ _ _ _ _ (hi 2) (hi 3), popped_frame,
              hi 0]
  | false =>
      rcases List.eq_nil_or_concat' pre with rfl | ⟨pre, last, rfl⟩
      · have hs : (stopped p d).stacks = d.stacks := by
          funext i
          simp [stopped, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
            StructuredProgram.State.ofCfg, execInstr,
            hc.outer]
          rw [← (show d.stacks (p.stack 2) = [] from by simpa using hc.outer),
            Function.update_eq_self]
        refine ⟨4, stopped p d, body_stop p callback d hc.descending
          (by simpa using hc.outer), ?_, ?_, ?_, ?_⟩
        · exact spec.stable d (stopped p d) (by intros; simp only [hs]) hI
        · simpa only [hs] using hb
        · intro hactive
          simp [stopped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
            StructuredProgram.State.ofCfg, execInstr] at hactive
        · intro q z hq hz i
          exact (short_prefix p hb (show 4 ≤ 13 by omega) q z hq hz i).trans
            (Nat.le_max_right _ _)
      · cases last with
        | none =>
            cases j with
            | zero =>
                apply short (body_prune p callback d hc.descending
                  (pre.map Option.isSome).reverse true (by simpa using hc.outer)
                  (by simpa using hc.budget)) (by omega) (cursor_pruned p n pre d hc)
                · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
                · simpa using hj
                · intro i hi
                  simp [pruned, testedOutside_stacks, backed, pushed_frame, popped_frame,
                    hi 0, hi 1, hi 2, hi 3]
            | succ j =>
                apply short (body_next_outer p callback d hc.descending
                  (pre.map Option.isSome).reverse (List.replicate j true) true true
                  (by simpa using hc.outer) (by simpa [List.replicate_succ] using hc.budget))
                  (by omega) (cursor_next_outer p n j pre d hc)
                · simpa using hn
                · simp at hj ⊢
                  omega
                · intro i hi
                  simp [testedOutside_stacks, backed, popped_frame, hi 1, hi 2, hi 3]
        | some bit =>
            cases bit with
            | false =>
                apply short (body_next_inner p callback d hc.descending
                  (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
                  (by simpa using hc.outer) (by simpa using hc.inner)) (by omega)
                  (cursor_next_inner p n (j + 1) pre d hc)
                · simpa using hn
                · simpa using hj
                · intro i hi
                  simp [backed, popped_frame, hi 2, hi 3]
            | true =>
                apply short (body_finish p callback d hc.descending
                  (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
                  (by simpa using hc.outer) (by simpa using hc.inner)) (by omega)
                  (cursor_finished p n (j + 1) pre d hc)
                · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
                · simp at hj ⊢
                  omega
                · intro i hi
                  simp [finished, backed, pushed_frame, popped_frame, hi 0, hi 1, hi 2, hi 3]

/-- The complete actual loop has a bound independent of the number of pairs.
The conserved depth and strict budget bound every DFS controller word. -/
theorem loop_stack_bound (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I) (hN : N ≤ B) (hJ : J ≤ B)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {steps : ℕ} {a b : State r s}
    (heval : Eval (.while (p.register 1) (body p callback)) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hcursor : a.regs (p.register 1) = true →
      ∃ n j pre down, Cursor p n (j + 1) pre down a ∧
        n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J) :
    ∀ q z, q ≤ steps →
      Trace (compiled (.while (p.register 1) (body p callback)) (p.stack 0) (p.stack 2)) q
        (a.withPC (some (compiled (.while (p.register 1) (body p callback))
          (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  let Inv := fun a : State r s => I a ∧ (∀ i, (a.stacks i).length ≤ B) ∧
    (a.regs (p.register 1) = true →
      ∃ n j pre down, Cursor p n (j + 1) pre down a ∧
        n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J)
  have hB : B ≤ max D (s * B + 13) := by
    have hs : 1 ≤ s := by have := (p.stack 0).isLt; omega
    have hm : B ≤ s * B := by simpa using Nat.mul_le_mul_right B hs
    exact hm.trans ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _))
  apply StructuredSpace.loop_stack_bound (body p callback) (p.register 1)
    (p.stack 0) (p.stack 2) Inv (max D (s * B + 13)) _ _ _ heval ⟨hIa, ha, hcursor⟩
  · intro d hd i
    exact (hd.2.1 i).trans hB
  · intro t d e he hd hactive
    obtain ⟨n, j, pre, down, hc, hn, hj⟩ := hd.2.2 hactive
    obtain ⟨t', e', he', hIe, hb', hc', _⟩ :=
      body_resources p callback output visit I C N J B D spec hN hJ hcallback hc hn hj hd.2.1 hd.1
    have heq := Eval.final_unique (p.stack 0) he he'
    subst e'
    exact ⟨hIe, hb', hc'⟩
  · intro t d e he hd hactive
    obtain ⟨n, j, pre, down, hc, hn, hj⟩ := hd.2.2 hactive
    obtain ⟨t', e', he', _, _, _, hp⟩ :=
      body_resources p callback output visit I C N J B D spec hN hJ hcallback hc hn hj hd.2.1 hd.1
    have heq := StreamResources.eval_steps_eq (p.stack 0) (p.stack 2) he he'
    subst t'
    exact hp

/-- Initialization, every DFS iteration, and the concrete final halt share one
space bound on the same actual source execution. Zero budget performs no
callback and is covered as well. -/
theorem program_stack_bound (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {steps : ℕ} {a b : State r s} (heval : Eval (command p callback) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hdepth : a.stacks (p.stack 0) = List.replicate N true)
    (hbudget : a.stacks (p.stack 1) = List.replicate J true)
    (houter : a.stacks (p.stack 2) = []) (hinner : a.stacks (p.stack 3) = []) :
    ∀ q z, q ≤ steps + 1 → Trace (program p callback) q
      (a.withPC (some (program p callback).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have hN : N ≤ B := by simpa [hdepth] using ha (p.stack 0)
  have hJ : J ≤ B := by simpa [hbudget] using ha (p.stack 1)
  apply StructuredSpace.compiled_halt_stack_bound heval (p.stack 0) (p.stack 2)
  change Eval (.seq _ _) steps a b at heval
  cases heval with
  | @seq first second n m a middle b hinit hwhile =>
      have hi := atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
        .copy (p.register 1) (p.register 3), .set (p.register 0) true] a
      have hmid : middle = initialized p a := Eval.final_unique (p.stack 0) hinit hi
      subst middle
      have hn : n = 3 := StreamResources.eval_steps_eq (p.stack 0) (p.stack 2) hinit hi
      subst n
      have hcursor : (initialized p a).regs (p.register 1) = true →
          ∃ n j pre down, Cursor p n (j + 1) pre down (initialized p a) ∧
            n + pre.length = N ∧ (j + 1) + pre.countP Option.isSome = J := by
        intro hactive
        cases J with
        | zero =>
            simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr,
              readRegs, hbudget] at hactive
        | succ J =>
            refine ⟨N, J, [], true, ?_, by simp, by simp⟩
            refine ⟨hdepth, hbudget, houter, hinner, ?_, hactive⟩
            simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr]
      have hloop := loop_stack_bound p callback output visit I C N J B D spec hN hJ
        hcallback hwhile ha (spec.stable a (initialized p a) (by intros; rfl) hIa) hcursor
      have hp : ∀ q z, q ≤ 3 → Trace (compiled
          (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
            .copy (p.register 1) (p.register 3), .set (p.register 0) true])
          (p.stack 0) (p.stack 2)) q
          (a.withPC (some (compiled
            (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
              .copy (p.register 1) (p.register 3), .set (p.register 0) true])
            (p.stack 0) (p.stack 2)).entry)) z →
          ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
        intro q z hq hz i
        exact (short_prefix p ha (show 3 ≤ 13 by omega) q z hq hz i).trans
          (Nat.le_max_right _ _)
      exact StructuredSpace.sequence_stack_bound hinit hwhile (p.stack 0) (p.stack 2)
        hp hloop (program p callback) (siteAddress (command p callback))
        (exitAddress (command p callback)) (compiled_site _ (p.stack 0) (p.stack 2))

/-- Exact callback fold, the measured pair-count budget, and every source
prefix bound hold for one and the same finite-program run. The concrete query
callback must instantiate the explicit correctness and resource contracts. -/
theorem program_resources (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (houtput : ∀ i, output ≠ p.stack i)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ) (spec : CallbackSpec p callback output visit C N I)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    (a : State r s) (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hdepth : a.stacks (p.stack 0) = List.replicate N true)
    (hbudget : a.stacks (p.stack 1) = List.replicate J true)
    (houter : a.stacks (p.stack 2) = []) (hinner : a.stacks (p.stack 3) = []) :
    ∃ t e, t ≤ cost C N J ∧ Trace (program p callback) t
      (a.withPC (some (program p callback).entry)) (e.withPC none) ∧
      e.stacks output = DifferencePairs.fold visit N J [] (a.stacks output) ∧
      (∀ i, e.stacks (p.stack i) = a.stacks (p.stack i)) ∧ I e ∧
      ∀ q z, q ≤ t → Trace (program p callback) q
        (a.withPC (some (program p callback).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  cases J with
  | zero =>
      have heval := command_eval_zero p callback a (by simpa using hbudget)
      refine ⟨5, initialized p a, by simp [cost],
        compiled_halt_trace heval (p.stack 0) (p.stack 2),
        by simp [DifferencePairs.fold], (fun _ => rfl),
        spec.stable a _ (fun _ _ => rfl) hIa, ?_⟩
      exact program_stack_bound p callback output visit I C N 0 B D spec hcallback
        heval ha hIa hdepth hbudget houter hinner
  | succ J =>
      obtain ⟨t, e, ht, heval, ho, hf, hIe⟩ := command_eval p callback output houtput
        visit C N J I spec a hdepth hbudget houter hinner hIa
      refine ⟨t + 1, e, ?_, compiled_halt_trace heval (p.stack 0) (p.stack 2), ho, hf, hIe,
        program_stack_bound p callback output visit I C N (J + 1) B D spec hcallback
          heval ha hIa hdepth hbudget houter hinner⟩
      have hc := DifferencePairs.calls_le N (J + 1) (Nat.succ_pos J)
      unfold cost
      nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace
