import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- These words are dead on head entry and owned by this rescan. -/
def controllerPorts : List (Fin 896) := [859, 860, 861, 883, 884]

/-- The fixed bank is kept opaque so elaboration never expands all of its
ports while checking generic trace lemmas. -/
private opaque workPortsData :
    {ports : List (Fin 896) //
      ports = List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts} :=
  ⟨List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts, rfl⟩

/-- A fixed finite bank in the program syntax, independent of input size. -/
def workPorts : List (Fin 896) := workPortsData.1

private theorem workPorts_eq :
    workPorts = List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts :=
  workPortsData.2

private theorem workPorts_nodup : workPorts.Nodup := by
  rw [workPorts_eq]
  decide

private theorem workPorts_length : workPorts.length = 61 := by
  rw [workPorts_eq]
  decide

theorem mem_workPorts (i : Fin 896) :
    i ∈ workPorts ↔ i.val < 56 ∨ i ∈ controllerPorts := by
  rw [workPorts_eq]
  simp only [List.mem_append]
  apply or_congr_left
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

def clearWork : Code := .seq (clear 31) (BankRoutines.clearCmd 31 0 1 workPorts)

def cleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks workPorts a.stacks⟩

def clearWorkCost (a : Data) : ℕ :=
  2 * (a.stacks 31).length + 3 +
    (2 * (workPorts.map (fun i => (clearStacks 31 a.stacks i).length)).sum + 186)

theorem clearWork_eval (a : Data) : Eval clearWork (clearWorkCost a) a (cleared a) := by
  have hfirst := clear_eval a 31
  have hrest := BankRoutines.clear_eval (31 : Fin 896) (0 : Fin 40) 1 workPorts
    workPorts_nodup
    (readRegs a.regs 0 1 none) (clearStacks 31 a.stacks) (by simp)
  have he : BankRoutines.clearBankStacks workPorts (clearStacks 31 a.stacks) =
      BankRoutines.clearBankStacks workPorts a.stacks := by
    funext i
    by_cases hi : i ∈ workPorts
    · simp [BankRoutines.clearBankStacks, hi]
    · have h31 : i ≠ 31 := by
        intro h
        subst i
        exact hi ((mem_workPorts 31).mpr (Or.inl (by decide)))
      simp [BankRoutines.clearBankStacks, clearStacks, hi, h31]
  have hrun := hfirst.seq hrest
  rw [he, readRegs_reset] at hrun
  simpa only [clearWork, clearWorkCost, cleared, workPorts_length] using hrun

theorem cleared_low (a : Data) (i : Fin 56) :
    (cleared a).stacks (i.castAdd 840) = [] :=
  BankRoutines.clearBankStacks_mem _ _ _ ((mem_workPorts _).mpr (Or.inl i.isLt))

theorem cleared_controller (a : Data) (i : Fin 896) (hi : i ∈ controllerPorts) :
    (cleared a).stacks i = [] :=
  BankRoutines.clearBankStacks_mem _ _ _ ((mem_workPorts _).mpr (Or.inr hi))

theorem cleared_frame (a : Data) (i : Fin 896) (hi : 56 ≤ i.val)
    (hc : i ∉ controllerPorts) :
    (cleared a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame _ _ _ (by
    rw [mem_workPorts]
    exact not_or.mpr ⟨by omega, hc⟩)

theorem clearWorkCost_le (a : Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) : clearWorkCost a ≤ 124 * bound + 189 := by
  have hsum : (workPorts.map (fun i => (clearStacks 31 a.stacks i).length)).sum ≤
      61 * bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      by_cases hi : i = 31
      · subst i
        simp [clearStacks]
      · simpa [clearStacks, hi] using hb i)).trans_eq
    simp [workPorts_eq, controllerPorts]
  have h31 := hb 31
  unfold clearWorkCost
  omega

private theorem bank_clear_prefix (ports : List (Fin 896)) {steps bound : ℕ}
    {a b : Data} (he : Eval (BankRoutines.clearCmd 31 0 1 ports) steps a b)
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled (BankRoutines.clearCmd 31 0 1 ports) 860 860) q
      (a.withPC (some (compiled (BankRoutines.clearCmd 31 0 1 ports) 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil => exact clear_space 31 he hb
  | cons p ps ih =>
      cases he with
      | seq hfirst hrest =>
          have hs := clear_space p hfirst hb
          have hmiddle := hs _ _ le_rfl (compiled_trace hfirst 860 860)
          exact seq_space hfirst hrest hs (ih hrest hmiddle)

/-- Paid entry cleanup never enlarges any caller stack, at any source prefix. -/
theorem clearWork_prefix {steps bound : ℕ} {a b : Data}
    (he : Eval clearWork steps a b) (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled clearWork 860 860) q
      (a.withPC (some (compiled clearWork 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  cases he with
  | seq hfirst hrest =>
      have hs := clear_space 31 hfirst hb
      have hmiddle := hs _ _ le_rfl (compiled_trace hfirst 860 860)
      exact seq_space hfirst hrest hs (bank_clear_prefix workPorts hrest hmiddle)

/-- The initial workspace cleanup is paid before the complete native scan.
The concrete assembly supplies its fixed accepted-assignment command. -/
def head (accepted : Code) : Code :=
  .seq clearWork (.call (HeadSumProgram.scanProgram accepted))

def headProgram (accepted : Code) := compiled (head accepted) 651 853

/-- The actual zero-filled ambient word contains the current raw candidate
at exactly the ascending head coordinates used by the matrix columns. -/
theorem zeroMerge_headOrder (p : ℕ → Bool) (n : ℕ)
    (bits : Fin (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count p n) → Bool) :
    ∃ current : Fin n → Bool,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge
        (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn bits) = List.ofFn current ∧
      ∀ i, current (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.headOrder p n i) = bits i := by
  let mask := List.ofFn (fun v : Fin n => p v.val)
  let xs := OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge mask (List.ofFn bits)
  have hs := OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.zeroMerge_spec mask (List.ofFn bits)
    (by simp [mask, HeadRepresentativeSemantics.headOrder_highCount])
  have hlen : xs.length = n := by simpa [xs, mask] using hs.1
  have hex : ∃ current : Fin xs.length → Bool, xs = List.ofFn current :=
    ⟨fun i => xs[i.val], (List.ofFn_getElem (xs := xs)).symm⟩
  rw [hlen] at hex
  obtain ⟨current, hcurrent⟩ := hex
  refine ⟨current, hcurrent, ?_⟩
  have hselect := hs.2.1
  change OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true mask xs = _ at hselect
  rw [hcurrent, HeadRepresentativeSemantics.selected_headOrder] at hselect
  exact congrFun (List.ofFn_injective hselect)

/-- The concrete overlay preserves the ambient coordinate count and changes
only the current head, using the existing representative/high baseline. -/
theorem prepared_head_assignment (a : Data) (rf : Fin 8 → Bool)
    (p : ℕ → Bool) (n : ℕ)
    (bits : Fin (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.count p n) → Bool)
    (baseline : Fin n → Bool)
    (hbits : a.stacks 859 = List.ofFn bits)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => p v.val))
    (hbase : a.stacks 869 = List.ofFn baseline) :
    ∃ current : Fin n → Bool,
      (∀ i, current (OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.headOrder p n i) = bits i) ∧
      (HighQueryAdapter.NativeOverlay.result
        (HighQueryAdapter.NativeOverlay.resetState a) rf).stacks 145 =
        List.ofFn (fun v => if p v.val then current v else baseline v) := by
  obtain ⟨current, hcurrent, hhead⟩ := zeroMerge_headOrder p n bits
  refine ⟨current, hhead, ?_⟩
  rw [HighQueryAdapter.NativeOverlay.prepared_assignment, hbits, hmask, hbase,
    hcurrent, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.merge_ofFn]

open CommandRegisterFrames

private theorem outside_castAdd {r k : ℕ} (i : Fin (r + k)) (hi : r ≤ i.val) :
    ¬ ∃ j : Fin r, j.castAdd k = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have := j.isLt
  simp only [Fin.val_castAdd] at hv
  omega

private theorem not_mem_union {α : Type*} [DecidableEq α] {a : α} {s t : Finset α}
    (hs : a ∉ s) (ht : a ∉ t) : a ∉ s ∪ t := by
  simpa only [Finset.mem_union, not_or] using And.intro hs ht

private theorem bank_clear_writes (tmp : Fin 896) (ports : List (Fin 896)) (i : Fin 40)
    (h0 : i ≠ 0) (h1 : i ≠ 1) :
    i ∉ writes (BankRoutines.clearCmd tmp 0 1 ports) := by
  induction ports with
  | nil => exact not_mem_clearProgram _ _ _ _ h0 h1
  | cons p ps ih =>
      exact not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1) ih

/-- The head controller writes only its explicit low registers. This static
fact applies to every prefix and composes with the concrete factor footprint. -/
theorem head_not_mem_writes (accepted : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (haccepted : i ∉ writes accepted) : i ∉ writes (head accepted) := by
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have h2 : i ≠ 2 := by intro h; subst i; omega
  have hcopy (src dst : Fin 896) : i ∉ writes (copy src dst) :=
    not_mem_copyProgram _ _ _ _ _ _ h0 h1
  have hclear (src : Fin 896) : i ∉ writes (clear src) :=
    not_mem_clearProgram _ _ _ _ h0 h1
  have hpower : i ∉ writes HeadSumProgram.power :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hseed : i ∉ writes HeadSumProgram.seed := by
    exact not_mem_union (hcopy _ _)
      (not_mem_union (hcopy _ _) (not_mem_union hpower (hclear _)))
  have hstage : i ∉ writes HeadEvaluationProgram.StagedGate.stage := by
    simp only [HeadEvaluationProgram.StagedGate.stage, writes]
    exact not_mem_union (hcopy _ _) (not_mem_union (hcopy _ _)
      (not_mem_union (hcopy _ _) (not_mem_union (hcopy _ _)
        (not_mem_union (hcopy _ _) (hcopy _ _)))))
  have hcleanup : i ∉ writes HeadEvaluationProgram.StagedGate.cleanup := by
    simp only [HeadEvaluationProgram.StagedGate.cleanup, writes]
    exact not_mem_union (hclear _) (not_mem_union (hclear _)
      (not_mem_union (hclear _) (not_mem_union (hclear _)
        (not_mem_union (hclear _) (hclear _)))))
  have hcall : i ∉ writes HeadEvaluationProgram.StagedGate.callGate :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi)
  have hgate : i ∉ writes HeadEvaluationProgram.StagedGate.command :=
    not_mem_union hstage (not_mem_union hcall hcleanup)
  have hinc : i ∉ writes (Counters.incrementCmd HeadSumProgram.cursorPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hbody : i ∉ writes (HeadSumProgram.body accepted) := by
    change i ∉ writes HeadEvaluationProgram.StagedGate.command ∪
      ((writes accepted ∪ ∅) ∪ writes (Counters.incrementCmd HeadSumProgram.cursorPorts))
    simp only [Finset.union_empty]
    exact not_mem_union hgate (not_mem_union haccepted hinc)
  have hzero : i ∉ writes (CounterForPrograms.zeroCmd HeadSumProgram.fuelPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hdec : i ∉ writes (CounterForPrograms.decrementCmd HeadSumProgram.fuelPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have htest : i ∉ writes (CounterForPrograms.testCmd HeadSumProgram.fuelPorts) := by
    change i ∉ writes (CounterForPrograms.zeroCmd HeadSumProgram.fuelPorts) ∪ {2}
    exact not_mem_union hzero (by simpa only [Finset.mem_singleton] using h2)
  have hloop : i ∉ writes (HeadSumProgram.command accepted) :=
    not_mem_union htest (not_mem_union hbody (not_mem_union hdec htest))
  have hfinal : i ∉ writes HeadSumProgram.finalize :=
    not_mem_liftCommand _ _ _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi)
  have hscan : i ∉ writes (HeadSumProgram.scan accepted) :=
    not_mem_union hseed (not_mem_union hloop hfinal)
  exact not_mem_union (not_mem_union (hclear _) (bank_clear_writes 31 workPorts i h0 h1))
    (not_mem_compiled _ _ _ i hscan)

theorem head_register_frame (accepted : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (haccepted : i ∉ writes accepted) {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size (head accepted) + 1)}
    (ht : Trace (headProgram accepted) steps a b) : b.regs i = a.regs i :=
  compiled_trace_register_frame _ _ _ ht i (head_not_mem_writes accepted i hi haccepted)

/-- Immediate dense addition and paid cache reset leave caller flags outside
the actual eight- and sixteen-register arithmetic embeddings untouched. -/
theorem accumulate_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HeadSumProgram.accumulate :=
  not_mem_union
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 8) (k := 32) i (by omega)))
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi))

theorem overlay_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HighQueryAdapter.NativeOverlay.prepare := by
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  exact not_mem_union
    (not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1)
      (bank_clear_writes _ _ _ h0 h1))
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 8) (k := 32) i (by omega)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
