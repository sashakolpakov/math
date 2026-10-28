import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! The fixed node loop consumes the producer's framed cursor. Each actual
node execution supplies its own emitted coefficient word; no uniform choice
of byte representatives across register states is required. The indexed
invariant carries the complete retained query context between nodes. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace

open BitProgram StructuredCalls

abbrev Data := State 40 896

/-- The actual initializer derives the first physical loop boundary from
the produced framed master, including an empty coefficient stream. -/
theorem initialized_boundary (a : Data) (nodes : List (List Bool)) (B : ℕ)
    (hn : a.stacks 300 = Encoding.encodeList id nodes)
    (hb : ∀ port, (a.stacks port).length ≤ B) :
    let start := QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)
    start.stacks 301 = Encoding.encodeList id nodes ∧
      start.stacks 307 = [] ∧ start.stacks 863 = [] ∧
      start.regs 37 = !nodes.isEmpty ∧ start.regs 38 = true ∧
      ∀ port, (start.stacks port).length ≤ B := by
  dsimp only
  have hw := QueryAssembler.Nodes.initialized_words a
  have hc : (QueryAssembler.Nodes.initialized a).stacks 301 =
      Encoding.encodeList id nodes := hw.1.trans hn
  have hg := QueryNodeFinish.guarded_test (QueryAssembler.Nodes.initialized a) nodes hc
  exact ⟨hc, hw.2.2.2.1, hw.2.2.2.2.2.2.2, hg.1, hg.2,
    QueryAssembler.Nodes.initialized_bound a B hb⟩

/-- Retained ring words, cache masters and high-assignment data outside the
listed physical writes pass through node initialization unchanged. -/
theorem initialized_frame (a : Data) (port : Fin 896)
    (hp : port ∉ [301,302,305,307,78,850,851,863]) :
    (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)).stacks port =
      a.stacks port :=
  QueryAssembler.Nodes.initialized_frame a port hp

/-- Induct on the number of physical node records still to be read. The
output list is a proof witness only; the machine retains the flat stream863.
All component prefixes share one cap, independent of the number of nodes. -/
theorem loop_eval_prefix (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (remaining index : ℕ) (a : Data) (hcount : index + remaining = nodes.length)
    (ha : I index a) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)), steps ≤ remaining * (C + 1) + 1 ∧
      Eval QueryStreamProgram.nodeLoop steps a b ∧ I nodes.length b ∧
      outputs.length = remaining ∧
      (∀ j (hj : j < outputs.length), P (index + j) outputs[j]) ∧
      b.stacks 863 = a.stacks 863 ++ outputs.flatten ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodeLoop 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodeLoop 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max B D := by
  induction remaining generalizing index a with
  | zero =>
    have hi : index = nodes.length := by omega
    subst index
    obtain ⟨_, _, hg, hb⟩ := hboundary nodes.length a ha
    have hg' : a.regs 37 = false := by simpa using hg
    have he : Eval QueryStreamProgram.nodeLoop 1 a a := .while_false hg'
    refine ⟨1, a, [], by simp, he, ha, rfl, ?_, by simp, ?_⟩
    · intro j hj
      simp at hj
    · exact StructuredSpace.while_false_stack_bound QueryStreamProgram.nodeBody 37 a hg'
        (fun port => (hb port).trans (Nat.le_max_left _ _))
        (compiled QueryStreamProgram.nodeLoop 0 0)
        (siteAddress QueryStreamProgram.nodeLoop) (exitAddress QueryStreamProgram.nodeLoop)
        (compiled_site QueryStreamProgram.nodeLoop 0 0)
  | succ remaining ih =>
    have hi : index < nodes.length := by omega
    obtain ⟨_, _, hg, _⟩ := hboundary index a ha
    have hnonempty : nodes.drop index ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp only [List.length_drop, List.length_nil] at hl
      omega
    have hg' : a.regs 37 = true := by
      rw [hg, List.isEmpty_eq_false_iff.mpr hnonempty]
      rfl
    obtain ⟨first, middle, bits, hfirst, he, hm, hbits, hout, hprefix⟩ := hnode index a hi ha
    obtain ⟨rest, final, outputs, hrest, ht, hf, hlen, hp, ho, hs⟩ :=
      ih (index + 1) middle (by omega) hm
    have hwhole : Eval QueryStreamProgram.nodeLoop (first + rest + 1) a final :=
      .while_true hg' he ht
    refine ⟨first + rest + 1, final, bits :: outputs, ?_, hwhole, hf, ?_, ?_, ?_, ?_⟩
    · simp only [Nat.succ_mul]
      omega
    · simp [hlen]
    · intro j hj
      cases j with
      | zero => simpa only [Nat.add_zero, List.getElem_cons_zero] using hbits
      | succ j =>
        have hj' : j < outputs.length := by simpa using hj
        simpa only [List.getElem_cons_succ, Nat.add_succ, Nat.succ_add] using hp j hj'
    · rw [ho, hout, List.flatten_cons, List.append_assoc]
    · exact StructuredSpace.while_true_stack_bound hg' he ht 0 0
        (fun p q hle htrace port =>
          (hprefix p q hle htrace port).trans (Nat.le_max_right _ _)) hs
        (compiled QueryStreamProgram.nodeLoop 0 0)
        (siteAddress QueryStreamProgram.nodeLoop) (exitAddress QueryStreamProgram.nodeLoop)
        (compiled_site QueryStreamProgram.nodeLoop 0 0)

/-- A single actual run emits all node words in order and halts with the
framed cursor empty, the exact unary node index, and the original boundary cap.
The final halt is included in both time and every-stack prefix bounds. -/
theorem loop_resources (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (a : Data) (ha : I 0 a) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)), steps ≤ nodes.length * (C + 1) + 2 ∧
      Trace (compiled QueryStreamProgram.nodeLoop 0 0) steps
        (a.withPC (some (compiled QueryStreamProgram.nodeLoop 0 0).entry)) (b.withPC none) ∧
      I nodes.length b ∧ outputs.length = nodes.length ∧
      (∀ j (hj : j < outputs.length), P j outputs[j]) ∧
      b.stacks 301 = [false] ∧ b.stacks 307 = List.replicate nodes.length true ∧
      b.regs 37 = false ∧ b.stacks 863 = a.stacks 863 ++ outputs.flatten ∧
      (∀ port, (b.stacks port).length ≤ B) ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodeLoop 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodeLoop 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max B D := by
  obtain ⟨steps, b, outputs, hc, he, hi, hl, hp, ho, hs⟩ :=
    loop_eval_prefix nodes I P B D C hboundary hnode nodes.length 0 a (by simp) ha
  obtain ⟨hcursor, hindex, hguard, hb⟩ := hboundary nodes.length b hi
  refine ⟨steps + 1, b, outputs, by omega, compiled_halt_trace he 0 0, hi, hl,
    ?_, ?_, hindex, ?_, ho, hb, StructuredSpace.compiled_halt_stack_bound he 0 0 hs⟩
  · simpa only [Nat.zero_add] using hp
  · simpa [Encoding.encodeList] using hcursor
  · simpa using hguard

/-- The physical guard only reads the cursor. Its single instruction cannot
enlarge either an active stack or a preserved caller word. -/
theorem guard_prefix_bound (a : Data) (B : ℕ)
    (ha : ∀ port, (a.stacks port).length ≤ B) :
    ∀ p q, p ≤ 1 →
      Trace (compiled QueryNodeFinish.guardCursor 0 0) p
        (a.withPC (some (compiled QueryNodeFinish.guardCursor 0 0).entry)) q →
      ∀ port, (q.stacks port).length ≤ B := by
  intro p q hp hq port
  have hc : p = 0 ∨ p = 1 := by omega
  rcases hc with rfl | rfl
  · cases hq
    exact ha port
  · have heq := trace_same_length_unique hq
      (compiled_trace (QueryNodeFinish.guardCursor_eval a) 0 0)
    rw [heq]
    exact ha port

/-- Paid cursor initialization and the real initial guard precede the same
node loop. Dirty entry buffers are charged by the existing initializer, and
the accumulated stream starts empty before the first node is evaluated. -/
theorem nodes_eval_prefix (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (a : Data) (ha : ∀ port, (a.stacks port).length ≤ B)
    (hi : I 0 (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a))) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)),
      steps ≤ 23 * B + nodes.length * (C + 1) + 32 ∧
      Eval QueryStreamProgram.nodes steps a b ∧
      I nodes.length b ∧ outputs.length = nodes.length ∧
      (∀ j (hj : j < outputs.length), P j outputs[j]) ∧
      b.stacks 301 = [false] ∧ b.stacks 307 = List.replicate nodes.length true ∧
      b.regs 37 = false ∧ b.stacks 863 = outputs.flatten ∧
      (∀ port, (b.stacks port).length ≤ B) ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodes 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodes 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max (919 * B + 31) D := by
  let initialized := QueryAssembler.Nodes.initialized a
  let start := QueryNodeFinish.guarded initialized
  obtain ⟨steps, b, outputs, hc, he, hI, hl, hp, ho, hs⟩ :=
    loop_eval_prefix nodes I P B D C hboundary hnode nodes.length 0 start (by simp) hi
  have hinit := QueryAssembler.Nodes.initialize_eval a
  have hguard := QueryNodeFinish.guardCursor_eval initialized
  have htotal : Eval QueryStreamProgram.nodes
      (QueryAssembler.Nodes.initializeCost a + (1 + steps)) a b :=
    hinit.seq (hguard.seq he)
  have hcost := QueryAssembler.Nodes.initializeCost_le a B ha
  have hstart : ∀ port, (initialized.stacks port).length ≤ B :=
    QueryAssembler.Nodes.initialized_bound a B ha
  have hsmall : B ≤ 919 * B + 31 := by omega
  have hguardspace := guard_prefix_bound initialized B hstart
  have hguardloop := StructuredSpace.sequence_stack_bound hguard he 0 0
    (fun p q hle ht port =>
      (hguardspace p q hle ht port).trans (hsmall.trans (Nat.le_max_left _ _)))
    (fun p q hle ht port => (hs p q hle ht port).trans (max_le_max_right D hsmall))
    (compiled (.seq QueryNodeFinish.guardCursor QueryStreamProgram.nodeLoop) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hinitspace : ∀ p q, p ≤ QueryAssembler.Nodes.initializeCost a →
      Trace (compiled QueryAssembler.Nodes.initializeNodes 0 0) p
        (a.withPC (some (compiled QueryAssembler.Nodes.initializeNodes 0 0).entry)) q →
      ∀ port, (q.stacks port).length ≤ max (919 * B + 31) D := by
    intro p q hp hq port
    have hb := StructuredSpace.local_stack_bound
      (compiled QueryAssembler.Nodes.initializeNodes 0 0)
      (steps := 23 * B + 30) (StreamResources.dataBits_le_mul _ ha)
      p q (hp.trans hcost) hq port
    exact hb.trans ((by omega : 896 * B + (23 * B + 30) ≤ 919 * B + 31).trans
      (Nat.le_max_left _ _))
  have hwhole := StructuredSpace.sequence_stack_bound hinit (hguard.seq he) 0 0
    hinitspace hguardloop (compiled QueryStreamProgram.nodes 0 0)
    (siteAddress QueryStreamProgram.nodes) (exitAddress QueryStreamProgram.nodes)
    (compiled_site QueryStreamProgram.nodes 0 0)
  obtain ⟨hcursor, hindex, htest, hb⟩ := hboundary nodes.length b hI
  refine ⟨_, b, outputs, ?_, htotal, hI, hl,
    ?_, ?_, hindex, ?_, ?_, hb, hwhole⟩
  · omega
  · simpa only [Nat.zero_add] using hp
  · simpa [Encoding.encodeList] using hcursor
  · simpa using htest
  · have hz : start.stacks 863 = [] :=
      (QueryAssembler.Nodes.initialized_words a).2.2.2.2.2.2.2
    simpa only [hz, List.nil_append] using ho

/-- Add the one actual halt step to the same initialized node run. -/
theorem nodes_resources (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (a : Data) (ha : ∀ port, (a.stacks port).length ≤ B)
    (hi : I 0 (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a))) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)),
      steps ≤ 23 * B + nodes.length * (C + 1) + 33 ∧
      Trace (compiled QueryStreamProgram.nodes 0 0) steps
        (a.withPC (some (compiled QueryStreamProgram.nodes 0 0).entry)) (b.withPC none) ∧
      I nodes.length b ∧ outputs.length = nodes.length ∧
      (∀ j (hj : j < outputs.length), P j outputs[j]) ∧
      b.stacks 301 = [false] ∧ b.stacks 307 = List.replicate nodes.length true ∧
      b.regs 37 = false ∧ b.stacks 863 = outputs.flatten ∧
      (∀ port, (b.stacks port).length ≤ B) ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodes 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodes 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max (919 * B + 31) D := by
  obtain ⟨steps, b, outputs, hc, he, hI, hl, hp, hcursor, hindex, htest, hout, hb, hs⟩ :=
    nodes_eval_prefix nodes I P B D C hboundary hnode a ha hi
  exact ⟨steps + 1, b, outputs, by omega, compiled_halt_trace he 0 0,
    hI, hl, hp, hcursor, hindex, htest, hout, hb,
    StructuredSpace.compiled_halt_stack_bound he 0 0 hs⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace
