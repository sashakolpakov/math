import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace

/-! Relational accumulator correctness for the existing four-stack pair DFS.
Only the proof invariant is generalized: the actual commands, branch order,
callback states and all-prefix space theorem are unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational

open BitProgram StructuredCalls DifferencePairsProgram
open StructuredProgram (Atom)

variable {r s : ℕ} {α : Type*}

/-- The callback returns an actual dictionary representing the next semantic
value. No uniform choice of dictionary bytes is required. -/
structure CallbackSpec (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ)
    (I : α → State r s → Prop) : Prop where
  stable : ∀ value d e,
    (∀ o, (∀ i, o ≠ p.stack i) → e.stacks o = d.stacks o) → I value d → I value e
  run : ∀ J pre value d, pre.length = N → Cursor p 0 (J+1) pre true d → I value d →
    ∃ t e, t ≤ C ∧ Eval callback t (popped p 0 2 d) e ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧ I (visit pre value) e

/-- Erasing the semantic value supplies exactly the existing resource
contract. Its auxiliary byte observation is the preserved depth controller;
the resource theorem does not require an off-controller output port. -/
theorem CallbackSpec.erased (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ) (I : α → State r s → Prop)
    (spec : CallbackSpec p callback visit C N I) :
    DifferencePairsProgram.CallbackSpec p callback (p.stack 0) (fun _ word => word)
      C N (fun d => ∃ value, I value d) := by
  constructor
  · intro d e hf hd
    obtain ⟨value,hvalue⟩ := hd
    exact ⟨value,spec.stable value d e hf hvalue⟩
  · intro J pre d hn hc hd
    obtain ⟨value,hvalue⟩ := hd
    obtain ⟨t,e,ht,he,hf,hI⟩ := spec.run J pre value d hn hc hvalue
    exact ⟨t,e,ht,he,hf,hf 0,visit pre value,hI⟩

/-- The same actual subtree traversal realizes the semantic fold, while its
dictionary witnesses may vary at every callback. -/
theorem subtree (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ)
    (I : α → State r s → Prop) (spec : CallbackSpec p callback visit C N I)
    (n J : ℕ) (pre : List (Option Bool)) (value : α) (d : State r s)
    (hsize : n + pre.length = N) (h : Cursor p n (J+1) pre true d) (hi : I value d) :
    ∃ t e, BodyTrace p callback t d e ∧ Cursor p n (J+1) pre false e ∧
      t ≤ (C+46)*DifferencePairs.calls n (J+1) ∧
      I (DifferencePairs.fold visit n (J+1) pre value) e := by
  induction n generalizing J pre value d with
  | zero =>
      obtain ⟨t,e,ht,he,hf,hIe⟩ := spec.run J pre value d (by simpa using hsize) h hi
      have hr : Cursor p 0 (J+1) pre false (returned p e) :=
        ⟨(hf 0).trans h.depth,(hf 1).trans h.budget,(hf 2).trans h.outer,
          (hf 3).trans h.inner,returned_descending p e,returned_active p e⟩
      refine ⟨t+6,returned p e,?_,hr,?_,?_⟩
      · simpa [Nat.add_assoc] using BodyTrace.single h.active
          (body_callback p callback d e h.descending (by simpa using h.depth) t he)
      · simp only [DifferencePairs.calls]
        omega
      · exact spec.stable _ e _ (fun _ _ => rfl) hIe
  | succ n ih =>
      have hs : n+(pre++[none]).length=N := by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize
      have hd := cursor_descend p n (J+1) pre d h
      have hid : I value (descended p d) := spec.stable value d _ (by
        intro o ho
        simp [descended,ho]) hi
      obtain ⟨t₀,e₀,he₀,hc₀,ht₀,hi₀⟩ := ih J (pre++[none]) value (descended p d) hs hd hid
      have hdtrace := BodyTrace.single h.active (body_descend p callback d h.descending true
        (List.replicate n true) (by simpa [List.replicate_succ] using h.depth))
      cases J with
      | zero =>
          have hb := body_prune p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse true
            (by simpa using hc₀.outer) (by simpa using hc₀.budget)
          have hr := cursor_pruned p n pre e₀ hc₀
          refine ⟨9+t₀+13,pruned p e₀,
            (hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb),hr,?_,?_⟩
          · simp only [DifferencePairs.calls,DifferencePairs.calls_zero]
            nlinarith
          · have hsemantic := spec.stable _ e₀ (pruned p e₀)
              (by intro o ho; simp [pruned,backed,ho]) hi₀
            simpa only [DifferencePairs.fold] using hsemantic
      | succ J =>
          have hb₁ := body_next_outer p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse (List.replicate J true) true true
            (by simpa using hc₀.outer) (by simpa [List.replicate_succ] using hc₀.budget)
          have hc₁ := cursor_next_outer p n J pre e₀ hc₀
          have hi₁ : I (DifferencePairs.fold visit n (J+2) (pre++[none]) value)
              (entered p true false (testedOutside p e₀)) :=
            spec.stable _ e₀ _ (by intro o ho; simp [testedOutside_stacks,backed,ho]) hi₀
          obtain ⟨t₁,e₁,he₁,hc₁',ht₁,hi₁'⟩ := ih J (pre++[some false]) _
            (entered p true false (testedOutside p e₀))
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize) hc₁ hi₁
          have hb₂ := body_next_inner p callback e₁ hc₁'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₁'.outer) (by simpa using hc₁'.inner)
          have hc₂ := cursor_next_inner p n (J+1) pre e₁ hc₁'
          have hi₂ := spec.stable _ e₁ (entered p true true (backed p e₁))
            (by intro o ho; simp [backed,ho]) hi₁'
          obtain ⟨t₂,e₂,he₂,hc₂',ht₂,hi₂'⟩ := ih J (pre++[some true]) _
            (entered p true true (backed p e₁))
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize) hc₂ hi₂
          have hb₃ := body_finish p callback e₂ hc₂'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₂'.outer) (by simpa using hc₂'.inner)
          have hr := cursor_finished p n (J+1) pre e₂ hc₂'
          refine ⟨9+t₀+14+t₁+12+t₂+11,finished p e₂,
            (((((hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb₁)).trans he₁).trans
              (BodyTrace.single hc₁'.active hb₂)).trans he₂).trans
              (BodyTrace.single hc₂'.active hb₃),hr,?_,?_⟩
          · simp only [DifferencePairs.calls]
            nlinarith
          · exact spec.stable _ e₂ _ (by intro o ho; simp [finished,backed,ho]) hi₂'

/-- Actual command execution and semantic accumulator correctness, before
the single compiler halt step. -/
theorem command_eval (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C n J : ℕ)
    (I : α → State r s → Prop) (spec : CallbackSpec p callback visit C n I)
    (value : α) (d : State r s)
    (hdepth : d.stacks (p.stack 0)=List.replicate n true)
    (hbudget : d.stacks (p.stack 1)=List.replicate (J+1) true)
    (he : d.stacks (p.stack 2)=[]) (hu : d.stacks (p.stack 3)=[]) (hi : I value d) :
    ∃ t e, t ≤ (C+46)*DifferencePairs.calls n (J+1)+9 ∧
      Eval (command p callback) t d e ∧
      (∀ i,e.stacks (p.stack i)=d.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit n (J+1) [] value) e := by
  have hcursor : Cursor p n (J+1) [] true (initialized p d) := by
    constructor
    · exact hdepth
    · exact hbudget
    · exact he
    · exact hu
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr]
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, BitProgram.readRegs, hbudget, List.replicate_succ]
  have hii : I value (initialized p d) := spec.stable value d _ (fun _ _ => rfl) hi
  obtain ⟨t,e,ht,hc,hb,hIe⟩ := subtree p callback visit C n I spec n J [] value
    (initialized p d) (by simp) hcursor hii
  have hend := body_stop p callback e hc.descending (by simpa using hc.outer)
  have hstop : (stopped p e).regs (p.register 1)=false := by
    simp [stopped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr]
  have hw := (ht.trans (BodyTrace.single hc.active hend)).while_eval hstop
  have hinit := atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3),.set (p.register 0) true] d
  have hall : Eval (command p callback) (t+9) d (stopped p e) := by
    simpa [command,initialized,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using hinit.seq hw
  refine ⟨t+9,stopped p e,by omega,hall,?_,?_⟩
  · intro i
    fin_cases i <;>
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, hc.depth, hc.budget, hc.outer, hc.inner, hdepth, hbudget,
        he, hu]
  · exact spec.stable _ e _ (by
      intro o ho
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, ho]) hIe

/-- Relational correctness, exact native time and all-prefix space refer to
one execution of the unchanged pair iterator, including J=0 and J>N. -/
theorem program_resources (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (I : α → State r s → Prop)
    (C N J B D : ℕ) (spec : CallbackSpec p callback visit C N I)
    (hcallback : ∀ value j pre a b t, pre.length=N →
      (j+1)+pre.countP Option.isSome=J → Cursor p 0 (j+1) pre true a → I value a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ elapsed z, elapsed ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) elapsed
        ((popped p 0 2 a).withPC (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    (value : α) (a : State r s) (ha : ∀ i, (a.stacks i).length ≤ B) (hi : I value a)
    (hdepth : a.stacks (p.stack 0)=List.replicate N true)
    (hbudget : a.stacks (p.stack 1)=List.replicate J true)
    (houter : a.stacks (p.stack 2)=[]) (hinner : a.stacks (p.stack 3)=[]) :
    ∃ t e, Eval (command p callback) t a e ∧ t + 1 ≤ cost C N J ∧
      Trace (program p callback) (t+1)
        (a.withPC (some (program p callback).entry)) (e.withPC none) ∧
      (∀ i,e.stacks (p.stack i)=a.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit N J [] value) e ∧
      ∀ elapsed z, elapsed ≤ t + 1 → Trace (program p callback) elapsed
        (a.withPC (some (program p callback).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have hex : ∃ t e, Eval (command p callback) t a e ∧ t + 1 ≤ cost C N J ∧
      (∀ i,e.stacks (p.stack i)=a.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit N J [] value) e := by
    cases J with
    | zero =>
        exact ⟨4,initialized p a,command_eval_zero p callback a (by simpa using hbudget),
          by simp [cost],fun _ => rfl,by
            simpa only [DifferencePairs.fold] using
              spec.stable value a (initialized p a) (fun _ _ => rfl) hi⟩
    | succ J =>
        obtain ⟨t,e,ht,he,hf,hIe⟩ := command_eval p callback visit C N J I spec value a
          hdepth hbudget houter hinner hi
        refine ⟨t,e,he,?_,hf,hIe⟩
        have hc := DifferencePairs.calls_le N (J+1) (Nat.succ_pos J)
        unfold cost
        nlinarith
  obtain ⟨t,e,he,ht,hf,hIe⟩ := hex
  refine ⟨t,e,he,ht,compiled_halt_trace he (p.stack 0) (p.stack 2),hf,hIe,?_⟩
  apply DifferencePairsSpace.program_stack_bound p callback (p.stack 0) (fun _ word => word)
    (fun d => ∃ value,I value d) C N J B D (spec.erased p callback visit C N I)
    ?_ he ha ⟨value,hi⟩ hdepth hbudget houter hinner
  intro j pre d b steps hn hj hc hd hb heval
  obtain ⟨v,hv⟩ := hd
  exact hcallback v j pre d b steps hn hj hc hv hb heval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational
