import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

private theorem clear_call_space (port : Fin 896) {steps B : ℕ} {a b : Data}
    (he : Eval (.call (StackRoutines.clearProgram port 0 1)) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ steps →
      Trace (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788) k
        (a.withPC (some (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 0 1)
        (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788)
        (siteAddress (.call (StackRoutines.clearProgram port 0 1)))
        (exitAddress (.call (StackRoutines.clearProgram port 0 1)))
        (compiled_site (.call (StackRoutines.clearProgram port 0 1)) 784 788) ht
      intro k c _ hc i
      exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
        port 0 1 hc i).trans (ha i)

private theorem clear_bank_space (ports : List (Fin 896)) {steps B : ℕ} {a b : Data}
    (he : Eval (BankRoutines.clearCmd 767 0 1 ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ steps →
      Trace (compiled (BankRoutines.clearCmd 767 0 1 ports) 784 788) k
        (a.withPC (some (compiled (BankRoutines.clearCmd 767 0 1 ports) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  induction ports generalizing steps a b with
  | nil => exact clear_call_space 767 he ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clear_call_space port first ha
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 784 788)
          exact StructuredSpace.sequence_stack_bound first second 784 788 hfirst
            (ih second hmiddle)
            (compiled (BankRoutines.clearCmd 767 0 1 (port :: rest)) 784 788)
            (siteAddress (BankRoutines.clearCmd 767 0 1 (port :: rest)))
            (exitAddress (BankRoutines.clearCmd 767 0 1 (port :: rest)))
            (compiled_site (BankRoutines.clearCmd 767 0 1 (port :: rest)) 784 788)

private opaque lowerPortsWrapped :
    {ports : List (Fin 896) // ports = (List.finRange 48).map (Fin.castAdd 848)} :=
  ⟨(List.finRange 48).map (Fin.castAdd 848), rfl⟩

/-- The fixed lower-bank ports, kept opaque to prevent routine theorem
checking from reducing the complete cleanup program. -/
def lowerPorts : List (Fin 896) := lowerPortsWrapped.1

theorem lowerPorts_eq : lowerPorts = (List.finRange 48).map (Fin.castAdd 848) :=
  lowerPortsWrapped.2

def clearLower : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 lowerPorts

def clearedLower (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks lowerPorts a.stacks⟩

def clearLowerSteps (a : Data) : ℕ :=
  2 * (lowerPorts.map (fun i => (a.stacks i).length)).sum + 147

private theorem mem_lowerPorts (i : Fin 896) : i ∈ lowerPorts ↔ i.val < 48 := by
  rw [lowerPorts_eq]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clearLower_eval (a : Data) (hs : a.stacks 767 = []) :
    Eval clearLower (clearLowerSteps a) a (clearedLower a) := by
  have hn : lowerPorts.Nodup := by
    rw [lowerPorts_eq]
    exact List.Nodup.map (Fin.castAdd_injective 48 848) (List.nodup_finRange 48)
  simpa [clearLower, clearedLower, clearLowerSteps, lowerPorts_eq] using
    BankRoutines.clear_eval 767 (0 : Fin 40) 1 lowerPorts hn a.regs a.stacks hs

theorem clearedLower_empty (a : Data) (i : Fin 896) (hi : i.val < 48) :
    (clearedLower a).stacks i = [] := by
  simp [clearedLower, BankRoutines.clearBankStacks, (mem_lowerPorts i).mpr hi]

theorem clearedLower_frame (a : Data) (i : Fin 896) (hi : 48 ≤ i.val) :
    (clearedLower a).stacks i = a.stacks i := by
  simp [clearedLower, BankRoutines.clearBankStacks, mem_lowerPorts, Nat.not_lt.mpr hi]

theorem clearLower_time (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    clearLowerSteps a ≤ 96 * B + 147 := by
  have hsum : (lowerPorts.map (fun i => (a.stacks i).length)).sum ≤ lowerPorts.length * B := by
    simpa only [List.length_map, smul_eq_mul] using
      (List.sum_le_length_nsmul (lowerPorts.map (fun i => (a.stacks i).length)) B (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact ha i))
  have hlen : lowerPorts.length = 48 := by simp [lowerPorts_eq]
  rw [hlen] at hsum
  unfold clearLowerSteps
  omega

theorem clearLower_space (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ clearLowerSteps a → Trace (compiled clearLower 784 788) k
      (a.withPC (some (compiled clearLower 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B :=
  clear_bank_space lowerPorts (clearLower_eval a hs) ha

def graphInputs : List Route := [(808,30),(800,31),(801,32),(812,33),(813,46)]

def localInputs : List Route := [(809,19),(811,20),(808,21),(810,46)]

def registers : Fin 16 ↪ Fin 40 := Fin.castAddEmb 24

def stackMap : Fin 48 ↪ Fin 896 := Fin.castAddEmb 848

def graphCall : Cmd 40 896 := .call
  (ProgramLinking.liftProgram (compiled SparseCodeSearch.graphSearch 46 29) registers stackMap)

def localCall : Cmd 40 896 := .call
  (ProgramLinking.liftProgram (compiled SparseCodeSearch.localSearch 46 18) registers stackMap)

def graphStage : Cmd 40 896 :=
  .seq (routes graphInputs) (.seq graphCall (.seq (route (29,816)) clearLower))

def localStage : Cmd 40 896 :=
  .seq (routes localInputs) (.seq localCall (.seq (route (18,815)) clearLower))

/-- Graph first, followed by the local code. The two matrices are retained in
physical815/816 while the same lower workspace is reused. -/
def searches : Cmd 40 896 := .seq graphStage localStage

theorem routes_bound (ps : List Route) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((routesState ps a).stacks i).length ≤ B := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
      apply ih
      intro i
      by_cases hi : i = p.2
      · subst i
        simpa [routed] using ha p.1
      · simpa [routed, hi] using ha i

theorem graphInputs_valid : ∀ p ∈ graphInputs, routeValid p := by
  intro p hp
  simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals unfold routeValid; decide

theorem localInputs_valid : ∀ p ∈ localInputs, routeValid p := by
  intro p hp
  simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals unfold routeValid; decide

private theorem graphInputs_frame (a : Data) (i : Fin 896)
    (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32) (h33 : i ≠ 33) (h46 : i ≠ 46) :
    (routesState graphInputs a).stacks i = a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals apply Ne.symm; assumption

private theorem localInputs_frame (a : Data) (i : Fin 896)
    (h19 : i ≠ 19) (h20 : i ≠ 20) (h21 : i ≠ 21) (h46 : i ≠ 46) :
    (routesState localInputs a).stacks i = a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals apply Ne.symm; assumption

theorem graph_prepared (a : Data) (D r : ℕ)
    (hblank : ∀ i : Fin 896, i.val < 48 → a.stacks i = [])
    (hD : a.stacks 808 = List.replicate D true)
    (hr : a.stacks 812 = List.replicate r true) :
    CodeChecks.GraphMatrixReady D r (a.stacks 800) (a.stacks 801)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks
        (routesState graphInputs a)) := by
  have empty (i : Fin 896) (hi : i.val < 48)
      (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32) (h33 : i ≠ 33) (h46 : i ≠ 46) :
      (routesState graphInputs a).stacks i = [] :=
    (graphInputs_frame a i h30 h31 h32 h33 h46).trans (hblank i hi)
  constructor
  · intro i
    apply empty _ (by change i.val < 48; omega)
    all_goals intro h; have := congrArg Fin.val h; change i.val = _ at this; omega
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed, hD]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed, hr]
  all_goals simp only [projectState, SparseCodeSearch.leafStacks, Function.comp_apply]
  all_goals apply empty
  all_goals decide

theorem local_prepared (a : Data) (t D d : ℕ)
    (hblank : ∀ i : Fin 896, i.val < 48 → a.stacks i = [])
    (ht : a.stacks 809 = List.replicate t true)
    (hd : a.stacks 811 = List.replicate d true)
    (hD : a.stacks 808 = List.replicate D true) :
    CodeChecks.LocalMatrixReady t D d
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks
        (routesState localInputs a)) := by
  have empty (i : Fin 896) (hi : i.val < 48)
      (h19 : i ≠ 19) (h20 : i ≠ 20) (h21 : i ≠ 21) (h46 : i ≠ 46) :
      (routesState localInputs a).stacks i = [] :=
    (localInputs_frame a i h19 h20 h21 h46).trans (hblank i hi)
  constructor
  · intro i
    apply empty _ (by change i.val < 48; omega)
    all_goals intro h; have := congrArg Fin.val h; change i.val = _ at this; omega
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, ht]
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, hd]
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, hD]
  all_goals simp only [projectState, SparseCodeSearch.leafStacks, Function.comp_apply]
  all_goals apply empty
  all_goals decide


theorem routes_space (ps : List Route) (hp : ∀ p ∈ ps, routeValid p)
    (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ routesCost ps a → Trace (compiled (routes ps) 784 788) k
      (a.withPC (some (compiled (routes ps) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  induction ps generalizing a with
  | nil => exact clear_call_space 767 (routes_eval [] hp a hs) ha
  | cons p ps ih =>
      have hvalid := hp p (by simp)
      have htail : ∀ q ∈ ps, routeValid q := fun q hq => hp q (by simp [hq])
      have htmp : (routed p a).stacks 767 = [] := by
        simpa [routed, hvalid.2.2.symm] using hs
      have hbound : ∀ i, ((routed p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p.2
        · subst i; simpa [routed] using ha p.1
        · simpa [routed, hi] using ha i
      exact StructuredSpace.sequence_stack_bound
        (route_eval p hvalid a hs) (routes_eval ps htail (routed p a) htmp) 784 788
        (NativeLeaf.route_space p hvalid (route_eval p hvalid a hs) hs ha)
        (ih htail (routed p a) htmp hbound)
        (compiled (routes (p :: ps)) 784 788) (siteAddress (routes (p :: ps)))
        (exitAddress (routes (p :: ps))) (compiled_site (routes (p :: ps)) 784 788)

def saveAndClear (source target : Fin 896) : Cmd 40 896 :=
  .seq (route (source, target)) clearLower

def savedAndCleared (source target : Fin 896) (a : Data) : Data :=
  clearedLower (routed (source, target) a)

def saveAndClearSteps (source target : Fin 896) (a : Data) : ℕ :=
  routeCost (source, target) a + clearLowerSteps (routed (source, target) a)

theorem saveAndClear_eval (source target : Fin 896) (hp : routeValid (source, target))
    (a : Data) (hs : a.stacks 767 = []) :
    Eval (saveAndClear source target) (saveAndClearSteps source target a)
      a (savedAndCleared source target a) := by
  have htmp : (routed (source, target) a).stacks 767 = [] := by
    simpa [routed, hp.2.2.symm] using hs
  exact (route_eval (source, target) hp a hs).seq (clearLower_eval _ htmp)

theorem saveAndClear_bound (source target : Fin 896) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((savedAndCleared source target a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i.val < 48
  · simp [savedAndCleared, clearedLower_empty _ i hi]
  · rw [savedAndCleared, clearedLower_frame _ i (by omega)]
    by_cases hit : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hit] using ha i

theorem saveAndClear_time (source target : Fin 896) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    saveAndClearSteps source target a ≤ 105 * B + 155 := by
  have hr : ∀ i, ((routed (source, target) a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hi] using ha i
  have hc := clearLower_time (routed (source, target) a) B hr
  have hsrc := ha source
  have htgt := ha target
  dsimp [saveAndClearSteps, routeCost]
  omega

theorem saveAndClear_space (source target : Fin 896) (hp : routeValid (source, target))
    (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ saveAndClearSteps source target a →
      Trace (compiled (saveAndClear source target) 784 788) k
        (a.withPC (some (compiled (saveAndClear source target) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  have htmp : (routed (source, target) a).stacks 767 = [] := by
    simpa [routed, hp.2.2.symm] using hs
  have hr : ∀ i, ((routed (source, target) a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hi] using ha i
  exact StructuredSpace.sequence_stack_bound
    (route_eval (source, target) hp a hs) (clearLower_eval _ htmp) 784 788
    (NativeLeaf.route_space (source, target) hp (route_eval (source, target) hp a hs) hs ha)
    (clearLower_space _ B htmp hr)
    (compiled (saveAndClear source target) 784 788) (siteAddress (saveAndClear source target))
    (exitAddress (saveAndClear source target)) (compiled_site (saveAndClear source target) 784 788)


theorem graph_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data)
    (hq : BinaryArithmetic.toNat (a.stacks 31) = SparseCode.gapDenom m occurrence)
    (hD : BinaryArithmetic.toNat (a.stacks 32) = SparseCode.degree m occurrence)
    (hready : CodeChecks.GraphMatrixReady (SparseCode.degree m occurrence)
      (SparseCode.dimension m occurrence) (a.stacks 31) (a.stacks 32)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
      steps ≤ SparseCodeSearch.graphTime A (SparseCode.degree m occurrence)
        (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length + 1 ∧
      Eval graphCall steps a out ∧ out.stacks 29 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
      (∀ i, i ≠ 29 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled graphCall 784 788) k
        (a.withPC (some (compiled graphCall 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (SparseCodeSearch.graphSpace A (SparseCode.degree m occurrence)
            (SparseCode.dimension m occurrence) (a.stacks 31).length (a.stacks 32).length) A := by
  obtain ⟨steps, small, Q, ht, he, hQ, hgood, _, hf, hb, hspace⟩ :=
    SparseCodeSearch.graph_parameters_runs hm hocc A (a.stacks 31) (a.stacks 32) hq hD
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a)
      hready (fun i => ha (SparseCodeSearch.leafStacks i)) hdim h40 h41 h42
  obtain ⟨out, hoe, hout, hframe, _, hprefix⟩ := SparseCodeSearch.leaf_call_resources
    SparseCodeSearch.graphSearch 29 a small he hf ha hspace
  refine ⟨steps + 1, out, Q, Nat.add_le_add_right ht 1, hoe, hout.trans hQ, hgood, hframe, ?_, hprefix⟩
  intro i
  by_cases hi : i = 29
  · subst i
    rw [show out.stacks 29 = small.stacks 29 from hout]
    exact hb 29
  · rw [hframe i hi]
    exact (ha i).trans (by unfold SparseCodeSearch.boundary; omega)

theorem local_call {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data)
    (hready : CodeChecks.LocalMatrixReady (SparseCode.localRows m occurrence)
      (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ SparseCodeSearch.localTime A (SparseCode.localRows m occurrence)
        (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 ∧
      Eval localCall steps a out ∧ out.stacks 18 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled localCall 784 788) k
        (a.withPC (some (compiled localCall 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
            (SparseCode.degree m occurrence)
            (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A := by
  obtain ⟨steps, small, Q, ht, he, hQ, hgood, _, hf, hb, hspace⟩ :=
    SparseCodeSearch.local_parameters_runs hm hocc A
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a)
      hready (fun i => ha (SparseCodeSearch.leafStacks i)) hdim h40 h41 h42
  obtain ⟨out, hoe, hout, hframe, _, hprefix⟩ := SparseCodeSearch.leaf_call_resources
    SparseCodeSearch.localSearch 18 a small he hf ha hspace
  refine ⟨steps + 1, out, Q, Nat.add_le_add_right ht 1, hoe, hout.trans hQ, hgood, hframe, ?_, hprefix⟩
  intro i
  by_cases hi : i = 18
  · subst i
    rw [show out.stacks 18 = small.stacks 18 from hout]
    exact hb 18
  · rw [hframe i hi]
    exact (ha i).trans (by unfold SparseCodeSearch.boundary; omega)


private theorem run_save_clear (routine : Cmd 40 896) (source target : Fin 896)
    (hslo : source.val < 48) (hthi : 48 ≤ target.val)
    (hp : routeValid (source, target)) {steps A P : ℕ} {a b : Data}
    (he : Eval routine steps a b) (hs : a.stacks 767 = [])
    (hf : ∀ i, i ≠ source → b.stacks i = a.stacks i)
    (hb : ∀ i, (b.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ steps → Trace (compiled routine 784 788) k
      (a.withPC (some (compiled routine 784 788).entry)) c → ∀ i, (c.stacks i).length ≤ P) :
    Eval (.seq routine (saveAndClear source target))
      (steps + saveAndClearSteps source target b) a (savedAndCleared source target b) ∧
    (savedAndCleared source target b).stacks target = b.stacks source ∧
    (∀ i : Fin 896, i.val < 48 → (savedAndCleared source target b).stacks i = []) ∧
    (∀ i : Fin 896, 48 ≤ i.val → i ≠ target →
      (savedAndCleared source target b).stacks i = a.stacks i) ∧
    (∀ i, ((savedAndCleared source target b).stacks i).length ≤ A) ∧
    ∀ k c, k ≤ steps + saveAndClearSteps source target b →
      Trace (compiled (.seq routine (saveAndClear source target)) 784 788) k
        (a.withPC (some (compiled (.seq routine (saveAndClear source target)) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ max P A := by
  have htmp : b.stacks 767 = [] := (hf 767 (by intro h; have := congrArg Fin.val h; simp at this; omega)).trans hs
  have he2 := saveAndClear_eval source target hp b htmp
  refine ⟨he.seq he2, ?_, ?_, ?_, saveAndClear_bound source target b A hb, ?_⟩
  · rw [savedAndCleared, clearedLower_frame _ target hthi]
    simp [routed]
  · intro i hi
    exact clearedLower_empty _ i hi
  · intro i hi hne
    rw [savedAndCleared, clearedLower_frame _ i hi]
    change Function.update b.stacks target (b.stacks source) i = a.stacks i
    rw [Function.update_of_ne hne]
    apply hf
    intro h; have := congrArg Fin.val h; omega
  · apply StructuredSpace.sequence_stack_bound he he2 784 788
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (saveAndClear_space source target hp b A htmp hb k c hk hc i).trans
        (Nat.le_max_right _ _))
      (compiled (.seq routine (saveAndClear source target)) 784 788)
      (siteAddress (.seq routine (saveAndClear source target)))
      (exitAddress (.seq routine (saveAndClear source target)))
      (compiled_site (.seq routine (saveAndClear source target)) 784 788)

private theorem route_run_save_clear (inputs : List Route) (routine : Cmd 40 896)
    (source target : Fin 896) (hinputs : ∀ p ∈ inputs, routeValid p)
    (hlower : ∀ p ∈ inputs, p.2.val < 48)
    (hslo : source.val < 48) (hthi : 48 ≤ target.val)
    (hp : routeValid (source, target)) {steps A B P : ℕ} {a b : Data}
    (he : Eval routine steps (routesState inputs a) b) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hf : ∀ i, i ≠ source → b.stacks i = (routesState inputs a).stacks i)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hspace : ∀ k c, k ≤ steps → Trace (compiled routine 784 788) k
      ((routesState inputs a).withPC (some (compiled routine 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ P) :
    Eval (.seq (routes inputs) (.seq routine (saveAndClear source target)))
      (routesCost inputs a + (steps + saveAndClearSteps source target b))
      a (savedAndCleared source target b) ∧
    (savedAndCleared source target b).stacks target = b.stacks source ∧
    (∀ i : Fin 896, i.val < 48 → (savedAndCleared source target b).stacks i = []) ∧
    (∀ i : Fin 896, 48 ≤ i.val → i ≠ target →
      (savedAndCleared source target b).stacks i = a.stacks i) ∧
    (∀ i, ((savedAndCleared source target b).stacks i).length ≤ B) ∧
    ∀ k c, k ≤ routesCost inputs a + (steps + saveAndClearSteps source target b) →
      Trace (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788) k
        (a.withPC (some (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ max A (max P B) := by
  have htmp : (routesState inputs a).stacks 767 = [] := by
    rw [routes_frame inputs a 767 (by
      intro p hp h
      have := hlower p hp
      have := congrArg Fin.val h
      simp at this
      omega)]
    exact hs
  obtain ⟨he2, hout, hblank, hframe, hbound, hprefix⟩ :=
    run_save_clear routine source target hslo hthi hp he htmp hf hb hspace
  refine ⟨(routes_eval inputs hinputs a hs).seq he2, hout, hblank, ?_, hbound, ?_⟩
  · intro i hi hne
    rw [hframe i hi hne]
    apply routes_frame
    intro p hp h
    have := hlower p hp
    have := congrArg Fin.val h
    omega
  · exact StructuredSpace.sequence_stack_bound (routes_eval inputs hinputs a hs) he2 784 788
      (fun k c hk hc i => (routes_space inputs hinputs a A hs ha k c hk hc i).trans
        (Nat.le_max_left _ _))
      (fun k c hk hc i => (hprefix k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788)
      (siteAddress (.seq (routes inputs) (.seq routine (saveAndClear source target))))
      (exitAddress (.seq (routes inputs) (.seq routine (saveAndClear source target))))
      (compiled_site (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788)


def graphStageTime (A m occurrence qlen Dlen : ℕ) : ℕ :=
  5 * (9 * A + 8) + 3 +
    (SparseCodeSearch.graphTime A (SparseCode.degree m occurrence)
      (SparseCode.dimension m occurrence) qlen Dlen + 1 +
      (105 * SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) + 155))

def graphStageSpace (A m occurrence qlen Dlen : ℕ) : ℕ :=
  max A (max (max (SparseCodeSearch.graphSpace A (SparseCode.degree m occurrence)
    (SparseCode.dimension m occurrence) qlen Dlen) A)
    (SparseCodeSearch.boundary A (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)))

theorem graph_stage {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hq : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m occurrence)
    (hDb : BinaryArithmetic.toNat (a.stacks 801) = SparseCode.degree m occurrence)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (hr : a.stacks 812 = List.replicate (SparseCode.dimension m occurrence) true)
    (hDr : a.stacks 813 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
      steps ≤ graphStageTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval graphStage steps a out ∧ out.stacks 816 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled graphStage 784 788) k
        (a.withPC (some (compiled graphStage 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ graphStageSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  have h31 : (routesState graphInputs a).stacks 31 = a.stacks 800 := by
    simp [graphInputs, routesState, routed]
  have h32 : (routesState graphInputs a).stacks 32 = a.stacks 801 := by
    simp [graphInputs, routesState, routed]
  have h46 : (routesState graphInputs a).stacks 46 = a.stacks 813 := by
    simp [graphInputs, routesState, routed]
  have hlow (i : Fin 896) (hi : i.val < 48) : a.stacks i = [] := hblank i (by omega)
  have hother (i : Fin 896) (hi : i = 40 ∨ i = 41 ∨ i = 42) :
      (routesState graphInputs a).stacks i = [] := by
    rcases hi with rfl | rfl | rfl
    all_goals rw [graphInputs_frame a _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    all_goals exact hblank _ (by decide)
  obtain ⟨steps, mid, Q, ht, he, hQ, hgood, hframe, hbound, hprefix⟩ :=
    graph_call hm hocc A (routesState graphInputs a) (by rw [h31]; exact hq)
      (by rw [h32]; exact hDb) (by
        rw [h31, h32]
        exact graph_prepared a _ _ hlow hD hr)
      (routes_bound graphInputs a A ha) (h46.trans hDr)
      (hother 40 (Or.inl rfl)) (hother 41 (Or.inr (Or.inl rfl)))
      (hother 42 (Or.inr (Or.inr rfl)))
  have hlower : ∀ p ∈ graphInputs, p.2.val < 48 := by
    intro p hp
    simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  obtain ⟨hexec, hout, hempty, hframe2, hb, hp⟩ := route_run_save_clear graphInputs graphCall
    29 816 graphInputs_valid hlower (by decide) (by decide) (by unfold routeValid; decide)
    he (hblank 767 (by decide)) ha hframe hbound hprefix
  refine ⟨_, _, Q, ?_, hexec, hout.trans hQ, hgood, ?_, ?_, hb, ?_⟩
  · have hroute := routes_cost_bound graphInputs a A ha
    have hsave := saveAndClear_time 29 816 mid _ hbound
    rw [h31, h32] at ht
    simpa only [graphStageTime, graphInputs, List.length_cons, List.length_nil] using
      Nat.add_le_add hroute (Nat.add_le_add ht hsave)
  · intro i hi
    by_cases hlo : i.val < 48
    · exact hempty i hlo
    · rw [hframe2 i (by omega) (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      exact hblank i hi
  · intro i hi hne
    exact hframe2 i (by omega) hne
  · simpa only [graphStage, graphStageSpace, saveAndClear, h31, h32] using hp


def localStageTime (A m occurrence : ℕ) : ℕ :=
  4 * (9 * A + 8) + 3 +
    (SparseCodeSearch.localTime A (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 +
      (105 * SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) + 155))

def localStageSpace (A m occurrence : ℕ) : ℕ :=
  max A (max (max (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
    (SparseCode.degree m occurrence)
    (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A)
    (SparseCodeSearch.boundary A (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)))

theorem local_stage {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (ht : a.stacks 809 = List.replicate (SparseCode.localRows m occurrence) true)
    (hd : a.stacks 811 = List.replicate
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) true)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (htD : a.stacks 810 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ localStageTime A m occurrence ∧
      Eval localStage steps a out ∧ out.stacks 815 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled localStage 784 788) k
        (a.withPC (some (compiled localStage 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ localStageSpace A m occurrence := by
  have h46 : (routesState localInputs a).stacks 46 = a.stacks 810 := by
    simp [localInputs, routesState, routed]
  have hlow (i : Fin 896) (hi : i.val < 48) : a.stacks i = [] := hblank i (by omega)
  have hother (i : Fin 896) (hi : i = 40 ∨ i = 41 ∨ i = 42) :
      (routesState localInputs a).stacks i = [] := by
    rcases hi with rfl | rfl | rfl
    all_goals rw [localInputs_frame a _ (by decide) (by decide) (by decide) (by decide)]
    all_goals exact hblank _ (by decide)
  obtain ⟨steps, mid, Q, htime, he, hQ, hgood, hframe, hbound, hprefix⟩ :=
    local_call hm hocc A (routesState localInputs a) (local_prepared a _ _ _ hlow ht hd hD)
      (routes_bound localInputs a A ha) (h46.trans htD)
      (hother 40 (Or.inl rfl)) (hother 41 (Or.inr (Or.inl rfl)))
      (hother 42 (Or.inr (Or.inr rfl)))
  have hlower : ∀ p ∈ localInputs, p.2.val < 48 := by
    intro p hp
    simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  obtain ⟨hexec, hout, hempty, hframe2, hb, hp⟩ := route_run_save_clear localInputs localCall
    18 815 localInputs_valid hlower (by decide) (by decide) (by unfold routeValid; decide)
    he (hblank 767 (by decide)) ha hframe hbound hprefix
  refine ⟨_, _, Q, ?_, hexec, hout.trans hQ, hgood, ?_, ?_, hb, hp⟩
  · have hroute := routes_cost_bound localInputs a A ha
    have hsave := saveAndClear_time 18 815 mid _ hbound
    simpa only [localStageTime, localInputs, List.length_cons, List.length_nil] using
      Nat.add_le_add hroute (Nat.add_le_add htime hsave)
  · intro i hi
    by_cases hlo : i.val < 48
    · exact hempty i hlo
    · rw [hframe2 i (by omega) (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      exact hblank i hi
  · intro i hi hne
    exact hframe2 i (by omega) hne


def graphBoundary (A m occurrence : ℕ) : ℕ := SparseCodeSearch.boundary A
  (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)

def searchBoundary (A m occurrence : ℕ) : ℕ := SparseCodeSearch.boundary
  (graphBoundary A m occurrence) (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)

def searchesTime (A m occurrence qlen Dlen : ℕ) : ℕ :=
  graphStageTime A m occurrence qlen Dlen + localStageTime (graphBoundary A m occurrence) m occurrence

def searchesSpace (A m occurrence qlen Dlen : ℕ) : ℕ :=
  max (graphStageSpace A m occurrence qlen Dlen)
    (localStageSpace (graphBoundary A m occurrence) m occurrence)

/-- Both searched matrices are physically retained for serialization. The
second search starts from the polynomial matrix boundary, independently of
how many losing candidates the first search visited. -/
theorem searches_eval {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hq : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m occurrence)
    (hDb : BinaryArithmetic.toNat (a.stacks 801) = SparseCode.degree m occurrence)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (ht : a.stacks 809 = List.replicate (SparseCode.localRows m occurrence) true)
    (htD : a.stacks 810 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (hd : a.stacks 811 = List.replicate
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) true)
    (hr : a.stacks 812 = List.replicate (SparseCode.dimension m occurrence) true)
    (hDr : a.stacks 813 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval searches steps a out ∧ out.stacks 816 = matrixFrames shifts ∧
      out.stacks 815 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ searchBoundary A m occurrence) ∧
      ∀ k c, k ≤ steps → Trace (compiled searches 784 788) k
        (a.withPC (some (compiled searches 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ searchesSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  obtain ⟨ng, g, shifts, hng, heg, hshifts, hgood, hgb, hgf, hgBound, hgSpace⟩ :=
    graph_stage hm hocc A a ha hblank hq hDb hD hr hDr
  have lg (i : Fin 896) (hi : i ≠ 816) (hhi : 768 ≤ i.val) : g.stacks i = a.stacks i := hgf i hhi hi
  obtain ⟨nl, out, Q, hnl, hel, hQ, hdist, houtblank, houtframe, houtbound, houtspace⟩ :=
    local_stage hm hocc (graphBoundary A m occurrence) g hgBound hgb
      ((lg 809 (by decide) (by decide)).trans ht)
      ((lg 811 (by decide) (by decide)).trans hd)
      ((lg 808 (by decide) (by decide)).trans hD)
      ((lg 810 (by decide) (by decide)).trans htD)
  refine ⟨ng + nl, out, shifts, Q, Nat.add_le_add hng hnl, heg.seq hel,
    (houtframe 816 (by decide) (by decide)).trans hshifts, hQ, hgood, hdist,
    houtblank, ?_, houtbound, ?_⟩
  · intro i hi h815 h816
    exact (houtframe i hi h815).trans (hgf i hi h816)
  · exact StructuredSpace.sequence_stack_bound heg hel 784 788
      (fun k c hk hc i => (hgSpace k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (houtspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled searches 784 788) (siteAddress searches) (exitAddress searches)
      (compiled_site searches 784 788)


/-- Runtime unary dimensions already occupy physical input words. Thus the
retained matrices add only a fixed linear factor to the original word cap. -/
theorem searchBoundary_physical (A m occurrence : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (htD : a.stacks 810 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (hDr : a.stacks 813 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true) :
    searchBoundary A m occurrence ≤ 13 * A + 2 := by
  have hlocal := ha 810
  have hgraph := ha 813
  rw [htD, List.length_replicate] at hlocal
  rw [hDr, List.length_replicate] at hgraph
  unfold searchBoundary graphBoundary SparseCodeSearch.boundary
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
