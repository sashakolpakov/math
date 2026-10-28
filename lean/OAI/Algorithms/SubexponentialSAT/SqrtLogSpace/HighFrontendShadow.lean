import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendState
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried

/-! The actual frontend has a query-only polynomial step budget. Selected
stack growth therefore bounds every visible output and every prefix without
charging any suspended caller word. This uses the original execution directly;
no new query evaluator or replacement run is introduced. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow

open BitProgram StructuredCalls SqrtLog HighMarkedFrontend

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

private theorem prefix_visible {l : ℕ} (p : Program 40 896 l)
    (a : State 40 896) (L budget : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L)
    {t : ℕ} {z : Cfg 40 896 l} (ht : t ≤ budget)
    (hz : Trace p t (a.withPC (some p.entry)) z) :
    ∀ i, ¬ H i → (z.stacks i).length ≤ L + budget := by
  intro i hi
  have hg := trace_selectedStackBits p {i} hz
  have hh : (z.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [selectedStackBits, Finset.sum_singleton] using hg
  exact hh.trans (Nat.add_le_add (ha i hi) ht)

/-- The actual source-only budget applies to this exact occurrence of the
marked command by determinism, with arbitrary retained caller words. -/
theorem marked_time (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome = true)
    (href : a.stacks 321 = q.index.reverse) (he : Eval (command k) steps a b) :
    steps + 1 ≤ budget q k := by
  obtain ⟨t,c,_,_,_,hactual,hcost,_⟩ := command_eval q k a hv hc hs hm href
  have ht := SubexpPrimeProgram.eval_steps_unique he hactual 321 338
  exact ht ▸ hcost

/-- Exact endpoint contents and guard facts remain those of he. Only their
visible lengths are bounded, by per-stack growth on the same compiled trace. -/
theorem marked_resources (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps L : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome = true)
    (href : a.stacks 321 = q.index.reverse) (he : Eval (command k) steps a b)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    steps + 1 ≤ budget q k ∧
      (∀ i, ¬ H i → (b.stacks i).length ≤ L + budget q k) ∧
      ∀ t z, t ≤ steps + 1 → Trace (program k) t
        (a.withPC (some (program k).entry)) z →
        ∀ i, ¬ H i → (z.stacks i).length ≤ L + budget q k := by
  have ht := marked_time q k a b steps hv hc hs hm href he
  have hp : ∀ t z, t ≤ steps + 1 → Trace (program k) t
      (a.withPC (some (program k).entry)) z →
      ∀ i, ¬ H i → (z.stacks i).length ≤ L + budget q k := by
    intro t z htz hz
    exact prefix_visible (program k) a L (budget q k) ha (htz.trans ht) hz
  exact ⟨ht, hp _ _ le_rfl (compiled_halt_trace he 321 338), hp⟩

private theorem lower_visible (i : Fin 768) (hi : ¬ LeafProgram.OuterCarried.hidden i) :
    ¬ H (stackMap i) := by
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
  change ¬ (i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
  have hh := i.isLt
  omega

/-- The exact physical FrontState and the visible lower-bank cap required by
NativeQueryPreparation.front_resources come from the same frontend Eval. -/
theorem marked_front_resources (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps L : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome = true)
    (href : a.stacks 321 = q.index.reverse) (he : Eval (command k) steps a b)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.markedInput (project a)) (project b) l w ∧
      steps + 1 ≤ budget q k ∧
      ∀ i, ¬ LeafProgram.OuterCarried.hidden i →
        ((project b).stacks i).length ≤ L + budget q k := by
  obtain ⟨l,w,hfront⟩ := command_front_state q k a b steps hv hc hs hm href he
  obtain ⟨ht,hb,_⟩ := marked_resources q k a b steps L hv hc hs hm href he ha
  exact ⟨l,w,hfront,ht,fun i hi => hb (stackMap i) (lower_visible i hi)⟩

theorem accepted_time (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b) :
    steps + 1 ≤ acceptedBudget q k := by
  obtain ⟨t,c,_,_,_,hactual,hcost,_⟩ := accepted_command_eval q k a hv hc hs hm hindex
  have ht := SubexpPrimeProgram.eval_steps_unique he hactual 700 338
  exact ht ▸ hcost

/-- The unmarked final frontend satisfies the same pointwise resource rule. -/
theorem accepted_resources (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps L : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    steps + 1 ≤ acceptedBudget q k ∧
      (∀ i, ¬ H i → (b.stacks i).length ≤ L + acceptedBudget q k) ∧
      ∀ t z, t ≤ steps + 1 → Trace (acceptedProgram k) t
        (a.withPC (some (acceptedProgram k).entry)) z →
        ∀ i, ¬ H i → (z.stacks i).length ≤ L + acceptedBudget q k := by
  have ht := accepted_time q k a b steps hv hc hs hm hindex he
  have hp : ∀ t z, t ≤ steps + 1 → Trace (acceptedProgram k) t
      (a.withPC (some (acceptedProgram k).entry)) z →
      ∀ i, ¬ H i → (z.stacks i).length ≤ L + acceptedBudget q k := by
    intro t z htz hz
    exact prefix_visible (acceptedProgram k) a L (acceptedBudget q k) ha (htz.trans ht) hz
  exact ⟨ht, hp _ _ le_rfl (compiled_halt_trace he 700 338), hp⟩

theorem accepted_front_resources (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data) (steps L : ℕ)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.unmarkedInput (project a)) (project b) l w ∧
      steps + 1 ≤ acceptedBudget q k ∧
      ∀ i, ¬ LeafProgram.OuterCarried.hidden i →
        ((project b).stacks i).length ≤ L + acceptedBudget q k := by
  obtain ⟨l,w,hfront⟩ := accepted_command_front_state q k a b steps hv hc hs hm hindex he
  obtain ⟨ht,hb,_⟩ := accepted_resources q k a b steps L hv hc hs hm hindex he ha
  exact ⟨l,w,hfront,ht,fun i hi => hb (stackMap i) (lower_visible i hi)⟩

/-- The real marked frontend preserves the spare denominator word required
by preparation; its entry emptiness follows from the actual clean workspace. -/
theorem marked_denominator_empty (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : Data) (steps : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome = true)
    (href : a.stacks 321 = q.index.reverse) (he : Eval (command k) steps a b) :
    b.stacks 728 = [] := by
  obtain ⟨l,w,hf⟩ := command_front_state q k a b steps hv hc hs hm href he
  change (project b).stacks 728 = []
  have hframe := hf.frame 728 (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide)
  exact hframe.trans ((LeafProgram.Query.markedInput_frame (project a) 728
    (by decide) (by decide) (by decide)).trans (hc 728 (by decide) (by decide)))

/-- The history-only frontend leaves the same actual preparation scratch empty. -/
theorem accepted_denominator_empty (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : Data) (steps : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b) :
    b.stacks 728 = [] := by
  obtain ⟨l,w,hf⟩ := accepted_command_front_state q k a b steps hv hc hs hm hindex he
  change (project b).stacks 728 = []
  have hframe := hf.frame 728 (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide)
  exact hframe.trans ((LeafProgram.Query.unmarkedInput_frame (project a) 728
    (by decide) (by decide)).trans (hc 728 (by decide) (by decide)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow
