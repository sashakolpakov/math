import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentLoop

namespace OAI.Algorithms

/-! Actual callback and ordered collection proofs for the fixed node loop. -/

namespace SubexponentialSAT.SubexpNodeMomentLoop

open BitProgram StructuredCalls SubexpScanPrimitives

/-- Linking the four actual per-node tables preserves their measured traces;
there is one additional halt for the linked table. -/
theorem pipeline_trace (cache template jobs phase : Stage)
    {n₀ n₁ n₂ n₃ : ℕ} {d₀ d₁ d₂ d₃ d₄ : LocalData}
    (hc : Trace cache.program n₀ (d₀.withPC (some cache.program.entry)) (d₁.withPC none))
    (ht : Trace template.program n₁ (d₁.withPC (some template.program.entry)) (d₂.withPC none))
    (hj : Trace jobs.program n₂ (d₂.withPC (some jobs.program.entry)) (d₃.withPC none))
    (hp : Trace phase.program n₃ (d₃.withPC (some phase.program.entry)) (d₄.withPC none)) :
    Trace (pipelineProgram cache template jobs phase) (n₀ + (n₁ + (n₂ + n₃)) + 1)
      (d₀.withPC (some (pipelineProgram cache template jobs phase).entry)) (d₄.withPC none) :=
  compiled_halt_trace (Eval.seq (Eval.call cache.program hc)
    (Eval.seq (Eval.call template.program ht)
      (Eval.seq (Eval.call jobs.program hj) (Eval.call phase.program hp)))) 78 102

private theorem high_ne (j : Fin 320) (hj : 256 ≤ j.val) (i : Fin 256) : j ≠ localPorts i :=
  (localPorts_ne_high i j hj).symm

private theorem restrict_update_at (s : Store) (i : Fin 256) (j : Fin 320)
    (v : List Bool) (h : localPorts i = j) :
    restrict (Function.update s j v) = Function.update (restrict s) i v := by
  subst j
  exact restrict_update s i v

def activation (d : Data) : Data :=
  afterTransfer (afterCopy d 302 303 0 1) 302 78 0 1

theorem activation_eval (d : Data) (bits : List Bool)
    (hs : d.stacks 302 = bits.reverse) (ht : d.stacks 305 = []) :
    Eval (.seq (copy 302 303) (transfer 302 78)) (10 * bits.length + 8) d (activation d) := by
  have hc := copy_eval d 302 303 305 0 1 (by decide) (by decide) (by decide) (by decide) ht
  have hm := transfer_eval (afterCopy d 302 303 0 1) 302 78 0 1 (by decide) (by decide)
  have hl : ((afterCopy d 302 303 0 1).stacks 302).length = bits.length := by
    simp [afterCopy, StackRoutines.copyStacks, hs]
  have h := Eval.seq hc hm
  simpa only [copy, transfer, activation, hl, hs, List.length_reverse,
    show ∀ n : ℕ, (7*n+5)+(3*n+3)=10*n+8 by omega] using h

theorem activation_stacks (d : Data) (bits : List Bool)
    (hs : d.stacks 302 = bits.reverse) (ht : d.stacks 78 = []) :
    (activation d).stacks = Function.update (Function.update (Function.update d.stacks
      303 (bits.reverse ++ d.stacks 303)) 302 []) 78 bits := by
  funext i
  by_cases h78 : i = 78
  · subst i
    simp [activation, afterTransfer, afterCopy, StackRoutines.transferStacks,
      StackRoutines.copyStacks, hs, ht]
  by_cases h302 : i = 302
  · subst i
    simp [activation, afterTransfer, afterCopy, StackRoutines.transferStacks,
      StackRoutines.copyStacks, hs, ht]
  by_cases h303 : i = 303
  · subst i
    simp [activation, afterTransfer, afterCopy, StackRoutines.transferStacks,
      StackRoutines.copyStacks, hs, ht]
  simp [activation, afterTransfer, afterCopy, StackRoutines.transferStacks,
    StackRoutines.copyStacks, h78, h302, h303]

theorem ready_recordState (workspace : LocalStore → Prop) (d : Data)
    (h : Ready workspace d) (v pr f : Bool) (src payload : List Bool) :
    Ready workspace (RecordPrograms.state ports d v pr f src payload) := by
  constructor
  · simpa only [restrict_recordState] using h.ok
  · simpa [RecordPrograms.state, ports] using h.theta
  · simpa [RecordPrograms.state, ports] using h.jet
  · simpa [RecordPrograms.state, ports] using h.shape
  · simpa [RecordPrograms.state, ports] using h.temporary

private theorem activation_local (workspace : LocalStore → Prop) (d : Data)
    (bits : List Bool) (h : Ready workspace d) (hs : d.stacks 302 = bits.reverse) :
    workspace (Function.update (restrict (activation d).stacks) 78 []) := by
  have he := activation_stacks d bits hs h.theta
  have hr : restrict (activation d).stacks = Function.update (restrict d.stacks) 78 bits := by
    rw [he, restrict_update_at _ 78 78 bits (by decide),
      restrict_update_high _ 302 [] (by decide),
      restrict_update_high _ 303 _ (by decide)]
  rw [hr, Function.update_idem]
  have hz : Function.update (restrict d.stacks) 78 [] = restrict d.stacks := by
    apply Function.update_eq_self_iff.mpr
    exact h.theta.symm
  rw [hz]
  exact h.ok

private theorem activation_low_frame (d : Data) (bits : List Bool)
    (hs : d.stacks 302 = bits.reverse) (ht : d.stacks 78 = [])
    (i : Fin 256) (hi : i ≠ 78) :
    (activation d).stacks (localPorts i) = d.stacks (localPorts i) := by
  rw [activation_stacks d bits hs ht]
  have h78 : localPorts i ≠ 78 := localPorts_injective.ne hi
  simp [h78, localPorts_ne_high i 302 (by decide), localPorts_ne_high i 303 (by decide)]

/-- Concrete activation, installed node computation, collection and cleanup.
Only the installed finite node program has a remaining local trace contract. -/
theorem callback_contract {l : ℕ} (worker : Program 16 256 l)
    (validNode : List Bool → Prop) (workspace : LocalStore → Prop)
    (shape : List Bool) (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker validNode workspace shape jet cost) :
    RecordPrograms.CallbackContractWithOn ports (callback worker) (fun _ => false)
      (callbackCost cost shape jet) (Ready workspace) (Effect jet) validNode := by
  intro bits tail base hv hb
  let d₀ := RecordPrograms.state ports base false true false tail bits.reverse
  have hr₀ : Ready workspace d₀ := ready_recordState workspace base hb _ _ _ _ _
  have hs₀ : d₀.stacks 302 = bits.reverse := by simp [d₀, RecordPrograms.state, ports]
  let d₁ := activation d₀
  have h₁ := activation_eval d₀ bits hs₀ hr₀.temporary
  have hs₁ := activation_stacks d₀ bits hs₀ hr₀.theta
  obtain ⟨n, hn, d₂, h₂, ht₂, hj₂, hs₂, hw₂, hbank₂, hhigh₂⟩ :=
    worker_eval worker validNode workspace shape jet cost contract bits d₁ hv
      (activation_local workspace d₀ bits hr₀ hs₀)
      (by simp [d₁, hs₁])
      (by simpa [d₁, hs₁] using hr₀.jet)
      (by simpa [d₁, hs₁] using hr₀.shape)
  let d₃ := afterTransfer d₂ 102 304 0 1
  let d₄ := clearOut d₃ 104
  let d₅ := resetState d₄
  have h₃ := transfer_eval d₂ 102 304 0 1 (by decide) (by decide)
  have h₄ := clear_eval d₃ 104
  have h₅ := resetFlags_eval d₄
  have hs₃ : d₃.stacks 104 = shape := by
    simpa [d₃, afterTransfer, StackRoutines.transferStacks] using hs₂
  have hr₅ : Ready workspace d₅ := by
    constructor
    · have he : restrict d₅.stacks =
          Function.update (Function.update (restrict d₂.stacks) 102 []) 104 [] := by
        change restrict (Function.update d₃.stacks 104 []) = _
        rw [restrict_update_at _ 104 104 [] (by decide)]
        change Function.update (restrict (Function.update (Function.update d₂.stacks
          102 []) 304 ((d₂.stacks 102).reverse ++ d₂.stacks 304))) 104 [] = _
        rw [restrict_update_high _ 304 _ (by decide),
          restrict_update_at _ 102 102 [] (by decide)]
      rw [he]
      exact hw₂
    · simpa [d₅, d₄, d₃, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks] using ht₂
    · simp [d₅, d₄, d₃, resetState, clearOut, afterTransfer, StackRoutines.transferStacks]
    · simp [d₅, d₄, resetState, clearOut]
    · have hh := hhigh₂ 305 (by decide)
      simpa [d₅, d₄, d₃, d₁, hs₁, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks] using hh.trans hr₀.temporary
  have h301 : d₅.stacks 301 = tail := by
    have hh := hhigh₂ 301 (by decide)
    change d₂.stacks 301 = (activation d₀).stacks 301 at hh
    rw [hs₁] at hh
    simpa [d₅, d₄, d₃, d₀, resetState, clearOut, afterTransfer,
      StackRoutines.transferStacks, RecordPrograms.state, ports] using hh
  have h302 : d₅.stacks 302 = [] := by
    have hh := hhigh₂ 302 (by decide)
    simpa [d₅, d₄, d₃, d₁, hs₁, resetState, clearOut, afterTransfer,
      StackRoutines.transferStacks] using hh
  have hregs : d₅.regs 13 = false ∧ d₅.regs 14 = true ∧ d₅.regs 15 = false := by
    simp [d₅, resetState]
  have hself : RecordPrograms.state ports d₅ false true false tail [] = d₅ :=
    RecordPrograms.state_eq_self ports d₅ _ _ _ _ _ hregs.1 hregs.2.1 hregs.2.2 h301 h302
  refine ⟨10 * bits.length + 8 + (n + (3 * (jet bits).length + 3 +
    (2 * shape.length + 3 + 3))), d₅, ?_, hr₅, ?_, ?_⟩
  · unfold callbackCost
    omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := hhigh₂ 303 (by decide)
      change d₂.stacks 303 = (activation d₀).stacks 303 at hh
      rw [hs₁] at hh
      simpa [d₅, d₄, d₃, d₀, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks, RecordPrograms.state, ports] using hh
    · have hh := hhigh₂ 304 (by decide)
      change d₂.stacks 304 = (activation d₀).stacks 304 at hh
      rw [hs₁] at hh
      simpa [d₅, d₄, d₃, d₀, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks, RecordPrograms.state, ports, hj₂] using
        congrArg (fun xs => (jet bits).reverse ++ xs) hh
    · intro i hi
      have h78 : i ≠ 78 := by intro h; subst i; norm_num [SourceBank, Fin.coe_ofNat_eq_mod] at hi
      have h102 : localPorts i ≠ 102 := by intro h; have hv' := congrArg Fin.val h; simp [SourceBank] at hi; simp only [localPorts_val] at hv'; omega
      have h104 : localPorts i ≠ 104 := by intro h; have hv' := congrArg Fin.val h; simp [SourceBank] at hi; simp only [localPorts_val] at hv'; omega
      have hm := hbank₂ i hi
      have ha := activation_low_frame d₀ bits hs₀ hr₀.theta i h78
      have hf : d₀.stacks (localPorts i) = base.stacks (localPorts i) := by
        simp [d₀, RecordPrograms.state, ports, localPorts_ne_high i 301 (by decide),
          localPorts_ne_high i 302 (by decide)]
      simpa [d₅, d₄, d₃, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks, h102, h104, localPorts_ne_high i 304 (by decide)] using
        hm.trans (ha.trans hf)
    · intro i hi h301' h302' h303' h304'
      have h78 : i ≠ 78 := high_ne i hi 78
      have h102 : i ≠ 102 := high_ne i hi 102
      have h104 : i ≠ 104 := high_ne i hi 104
      have hm : d₁.stacks i = base.stacks i := by
        change (activation d₀).stacks i = _
        rw [hs₁]
        simp [d₀, RecordPrograms.state, ports, h78, h301', h302', h303']
      have hh := (hhigh₂ i hi).trans hm
      simpa [d₅, d₄, d₃, resetState, clearOut, afterTransfer,
        StackRoutines.transferStacks, h102, h104, h304'] using hh
  · rw [hself]
    have hm : Eval (transfer 102 304) (3 * (jet bits).length + 3) d₂ d₃ := by
      simpa only [hj₂, transfer] using h₃
    have hc : Eval (clear 104) (2 * shape.length + 3) d₃ d₄ := by
      simpa only [hs₃] using h₄
    exact Eval.seq h₁ (Eval.seq h₂ (Eval.seq hm (Eval.seq hc h₅)))

def accumulators (d : Data) : List Bool × List Bool := (d.stacks 303, d.stacks 304)

def prependResult (jet : List Bool → List Bool) (acc : List Bool × List Bool)
    (bits : List Bool) : List Bool × List Bool :=
  (bits.reverse ++ acc.1, (jet bits).reverse ++ acc.2)

theorem fold_prependResult (jet : List Bool → List Bool) (records : List (List Bool))
    (nodes jets : List Bool) :
    records.foldl (prependResult jet) (nodes, jets) =
      (records.flatten.reverse ++ nodes, (records.map jet).flatten.reverse ++ jets) := by
  induction records generalizing nodes jets with
  | nil => simp
  | cons bits rest ih =>
      simp only [List.foldl_cons, prependResult]
      rw [ih]
      simp only [List.flatten_cons, List.map_cons, List.reverse_append, List.append_assoc]

theorem visits_accumulators (jet : List Bool → List Bool) {records : List (List Bool)}
    {d out : Data} (h : RecordPrograms.Visits (fun _ => false) (Effect jet) records d out) :
    accumulators out =
      (records.flatten.reverse ++ d.stacks 303, (records.map jet).flatten.reverse ++ d.stacks 304) := by
  have he := h.fold_of_false (by intros; rfl) accumulators (prependResult jet)
    (by intro bits a b hb; exact Prod.ext hb.1 hb.2.1)
  rw [he]
  exact fold_prependResult jet records _ _

theorem visits_sourceBank (jet : List Bool → List Bool) {records : List (List Bool)}
    {d out : Data} (h : RecordPrograms.Visits (fun _ => false) (Effect jet) records d out)
    (i : Fin 256) (hi : SourceBank i) : out.stacks (localPorts i) = d.stacks (localPorts i) := by
  have he := h.fold_of_false (by intros; rfl) (fun x => x.stacks (localPorts i))
    (fun acc _ => acc) (by intro bits a b hb; exact hb.2.2.1 i hi)
  simpa using he

theorem visits_high (jet : List Bool → List Bool) {records : List (List Bool)}
    {d out : Data} (h : RecordPrograms.Visits (fun _ => false) (Effect jet) records d out)
    (i : Fin 320) (hi : 256 ≤ i.val)
    (h301 : i ≠ 301) (h302 : i ≠ 302) (h303 : i ≠ 303) (h304 : i ≠ 304) :
    out.stacks i = d.stacks i := by
  have he := h.fold_of_false (by intros; rfl) (fun x => x.stacks i)
    (fun acc _ => acc) (by intro bits a b hb; exact hb.2.2.2 i hi h301 h302 h303 h304)
  simpa using he

private theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [List.any_cons, Bool.false_or] using ih

private theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa [RecordPrograms.unread] using ih

/-- The collector visits every actual framed record and records its effects
in order, using the proved concrete callback above. -/
theorem loop_eval {l : ℕ} (worker : Program 16 256 l)
    (validNode : List Bool → Prop) (workspace : LocalStore → Prop)
    (shape : List Bool) (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker validNode workspace shape jet cost)
    (records : List (List Bool)) (d : Data)
    (hv : ∀ bits ∈ records, validNode bits) (hr : Ready workspace d)
    (hs : d.stacks 301 = Encoding.encodeList id records) (hp : d.stacks 302 = []) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost cost shape jet) records,
      ∃ out : Data, Eval (loop worker) n d out ∧ Ready workspace out ∧
        out.stacks 301 = [] ∧ out.stacks 302 = [] ∧
        accumulators out =
          (records.flatten.reverse ++ d.stacks 303,
            (records.map jet).flatten.reverse ++ d.stacks 304) ∧
        (∀ i : Fin 256, SourceBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) ∧
        (∀ i : Fin 320, 256 ≤ i.val → i ≠ 301 → i ≠ 302 → i ≠ 303 → i ≠ 304 →
          out.stacks i = d.stacks i) := by
  obtain ⟨n, next, hn, hnext, hist, he⟩ := RecordPrograms.iterate_run_with_on ports
    (callback worker) (fun _ => false) (callbackCost cost shape jet) (Ready workspace)
    (Effect jet) validNode (callback_contract worker validNode workspace shape jet cost contract)
    records [] d hv hr (d.regs 13) (d.regs 14) (d.regs 15)
  have hin : RecordPrograms.state ports d (d.regs 13) (d.regs 14) (d.regs 15)
      (Encoding.encodeList id records ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa only [ports, List.append_nil] using hs
    · exact hp
  let out := RecordPrograms.state ports next false true false [] []
  have hout : RecordPrograms.state ports next false true (records.any (fun _ => false))
      (RecordPrograms.unread (fun _ => false) records []) [] = out := by
    simp [out, unread_false, any_false]
  refine ⟨n, hn, out, ?_, ready_recordState workspace next hnext _ _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hin, hout, loop] using he
  · simp [out, RecordPrograms.state, ports]
  · simp [out, RecordPrograms.state, ports]
  · simpa [accumulators, out, RecordPrograms.state, ports] using visits_accumulators jet hist
  · intro i hi
    have hh := visits_sourceBank jet hist i hi
    simpa [out, RecordPrograms.state, ports,
      localPorts_ne_high i 301 (by decide), localPorts_ne_high i 302 (by decide)] using hh
  · intro i hi h301 h302 h303 h304
    have hh := visits_high jet hist i hi h301 h302 h303 h304
    simpa [out, RecordPrograms.state, ports, h301, h302] using hh

def totalCost (cost : List Bool → ℕ) (shape : List Bool)
    (jet : List Bool → List Bool) (records : List (List Bool)) : ℕ :=
  7 * (Encoding.encodeList id records).length +
    RecordPrograms.budget (callbackCost cost shape jet) records +
    3 * records.flatten.length + 3 * (records.map jet).flatten.length + 14

/-- Ordered physical output for the entire node list. This theorem is
conditional only on the explicitly installed local finite-node program's
trace contract; it does not assert that the pending producer joins exist. -/
theorem command_eval {l : ℕ} (worker : Program 16 256 l)
    (validNode : List Bool → Prop) (workspace : LocalStore → Prop)
    (shape : List Bool) (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker validNode workspace shape jet cost)
    (records : List (List Bool)) (d : Data)
    (hv : ∀ bits ∈ records, validNode bits) (hr : Ready workspace d)
    (hm : d.stacks 300 = Encoding.encodeList id records)
    (h301 : d.stacks 301 = []) (h302 : d.stacks 302 = [])
    (h303 : d.stacks 303 = []) (h304 : d.stacks 304 = [])
    (h256 : d.stacks 256 = []) (h265 : d.stacks 265 = []) :
    ∃ n ≤ totalCost cost shape jet records, ∃ out : Data,
      Eval (command worker) n d out ∧ Ready workspace out ∧
      out.stacks 256 = records.flatten ∧ out.stacks 265 = (records.map jet).flatten ∧
      out.stacks 300 = d.stacks 300 ∧
      out.stacks 301 = [] ∧ out.stacks 302 = [] ∧
      out.stacks 303 = [] ∧ out.stacks 304 = [] ∧
      (∀ i : Fin 256, SourceBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) := by
  let d₁ := afterCopy d 300 301 0 1
  have h₁ := copy_eval d 300 301 305 0 1 (by decide) (by decide) (by decide) (by decide) hr.temporary
  have hs₁ : d₁.stacks = Function.update d.stacks 301 (Encoding.encodeList id records) := by
    simp [d₁, afterCopy, StackRoutines.copyStacks, hm, h301]
  have hr₁ : Ready workspace d₁ := by
    constructor
    · rw [hs₁, restrict_update_high _ 301 _ (by decide)]
      exact hr.ok
    · simpa [hs₁] using hr.theta
    · simpa [hs₁] using hr.jet
    · simpa [hs₁] using hr.shape
    · simpa [hs₁] using hr.temporary
  obtain ⟨n, hn, d₂, h₂, hr₂, h301₂, h302₂, hacc₂, hbank₂, hhigh₂⟩ :=
    loop_eval worker validNode workspace shape jet cost contract records d₁ hv hr₁
      (by simp [hs₁]) (by simpa [hs₁] using h302)
  have h303₂ : d₂.stacks 303 = records.flatten.reverse := by
    simpa [accumulators, hs₁, h303] using congrArg Prod.fst hacc₂
  have h304₂ : d₂.stacks 304 = (records.map jet).flatten.reverse := by
    simpa [accumulators, hs₁, h304] using congrArg Prod.snd hacc₂
  have h256₂ : d₂.stacks 256 = [] := by
    simpa [hs₁, h256] using hhigh₂ 256 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h265₂ : d₂.stacks 265 = [] := by
    simpa [hs₁, h265] using hhigh₂ 265 (by decide) (by decide) (by decide) (by decide) (by decide)
  let d₃ := afterTransfer d₂ 303 256 0 1
  let d₄ := afterTransfer d₃ 304 265 0 1
  have h₃ := transfer_eval d₂ 303 256 0 1 (by decide) (by decide)
  have h₄ := transfer_eval d₃ 304 265 0 1 (by decide) (by decide)
  have hs₃ : d₃.stacks = Function.update (Function.update d₂.stacks 303 []) 256 records.flatten := by
    simp [d₃, afterTransfer, StackRoutines.transferStacks, h303₂, h256₂]
  have hs₄ : d₄.stacks = Function.update (Function.update d₃.stacks 304 []) 265
      (records.map jet).flatten := by
    simp [d₄, afterTransfer, StackRoutines.transferStacks, hs₃, h304₂, h265₂]
  have hl₄ : (d₃.stacks 304).length = (records.map jet).flatten.length := by
    simp [hs₃, h304₂]
  refine ⟨7 * (d.stacks 300).length + 5 +
      (n + (3 * (d₂.stacks 303).length + 3 + (3 * (d₃.stacks 304).length + 3))),
    ?_, d₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hm, h303₂, List.length_reverse, hl₄]
    unfold totalCost
    omega
  · exact Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  · have hrestrict : restrict d₄.stacks = restrict d₂.stacks := by
      rw [hs₄, hs₃, restrict_update_high _ _ _ (by decide),
        restrict_update_high _ _ _ (by decide), restrict_update_high _ _ _ (by decide),
        restrict_update_high _ _ _ (by decide)]
    constructor
    · simpa only [hrestrict] using hr₂.ok
    · simpa [hs₄, hs₃] using hr₂.theta
    · simpa [hs₄, hs₃] using hr₂.jet
    · simpa [hs₄, hs₃] using hr₂.shape
    · simpa [hs₄, hs₃] using hr₂.temporary
  · simp [hs₄, hs₃]
  · simp [hs₄]
  · have hh := hhigh₂ 300 (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [hs₄, hs₃, hs₁] using hh
  · simpa [hs₄, hs₃] using h301₂
  · simpa [hs₄, hs₃] using h302₂
  · simp [hs₄, hs₃]
  · simp [hs₄]
  · intro i hi
    simpa [hs₄, hs₃, hs₁, localPorts_ne_high i 265 (by decide),
      localPorts_ne_high i 304 (by decide), localPorts_ne_high i 256 (by decide),
      localPorts_ne_high i 303 (by decide), localPorts_ne_high i 301 (by decide)] using hbank₂ i hi

/-- The final halt and all table instructions count toward the bound. -/
theorem program_runs {l n bound : ℕ} (worker : Program 16 256 l) {d out : Data}
    (h : Eval (command worker) n d out) (hn : n ≤ bound) :
    RunsIn (program worker) (bound + 1)
      (d.withPC (some (program worker).entry)) (out.withPC none) :=
  ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace h 300 265⟩

theorem primitive_execution {l n bound : ℕ} (worker : Program 16 256 l) {d out : Data}
    (h : Eval (command worker) n d out) (hn : n ≤ bound) :
    Computation.RunsIn (BitProgram.primitive (program worker)).step
      (BitProgram.primitiveOverhead (program worker) * (bound + 1))
      (BitProgram.primitiveCfg (program worker) (d.withPC (some (program worker).entry)))
      (BitProgram.primitiveCfg (program worker) (out.withPC none)) :=
  BitProgram.primitive_execution _ (program_runs worker h hn)

end SubexponentialSAT.SubexpNodeMomentLoop

end OAI.Algorithms
