import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCacheProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def lowPorts : List (Fin 896) := List.ofFn (fun i : Fin 56 => i.castAdd 840)
def entryPorts : List (Fin 896) := lowPorts ++ [841]

theorem mem_lowPorts (i : Fin 896) : i ∈ lowPorts ↔ i.val < 56 := by
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

def clearBank (ports : List (Fin 896)) : Code :=
  liftCommand (clearMany ports) 841 841 FactorAssignmentProgram.localRegister id

noncomputable def cleared (ports : List (Fin 896)) (a : Data) : Data :=
  embedState FactorAssignmentProgram.localRegister id a
    (clearManyState ports (projectState FactorAssignmentProgram.localRegister id a))

def clearCost (ports : List (Fin 896)) (a : Data) : ℕ :=
  clearManyCost ports (projectState FactorAssignmentProgram.localRegister id a) + 1

theorem clear_eval (ports : List (Fin 896)) (a : Data) :
    Eval (clearBank ports) (clearCost ports a) a (cleared ports a) :=
  eval_liftCommand_from_state (clearMany ports) 841 841
    FactorAssignmentProgram.localRegister id a (Fin.castAdd_injective _ _)
    Function.injective_id (clearMany_eval ports _)

theorem cleared_stacks (ports : List (Fin 896)) (a : Data) (i : Fin 896) :
    (cleared ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  exact (embedState_stack FactorAssignmentProgram.localRegister id a
    (clearManyState ports (projectState FactorAssignmentProgram.localRegister id a))
    Function.injective_id i).trans (clearMany_stacks ports _ i)

theorem cleared_bound (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : WordBound B (cleared ports a) := by
  intro i
  rw [cleared_stacks]
  split_ifs
  · simp
  · exact ha i

theorem clearCost_le (ports : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : WordBound B a) : clearCost ports a ≤ ports.length * (2 * B + 3) + 1 :=
  Nat.add_le_add_right (clearManyCost_le ports _ B ha) 1

def finish : Code := .seq (QueryTupleVisitor.overwrite 69 852)
  (.seq (QueryTupleVisitor.overwrite 703 869) (clearBank lowPorts))

noncomputable def copied (a : Data) : Data :=
  QueryTupleVisitor.overwriteState 703 869 (QueryTupleVisitor.overwriteState 69 852 a)

noncomputable def finished (a : Data) : Data := cleared lowPorts (copied a)

noncomputable def finishCost (a : Data) : ℕ :=
  2 * (a.stacks 852).length + 7 * (a.stacks 69).length + 8 +
    (2 * (a.stacks 869).length + 7 * (a.stacks 703).length + 8 +
      clearCost lowPorts (copied a))

theorem finish_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval finish (finishCost a) a (finished a) := by
  have h1 := QueryTupleVisitor.overwrite_eval 69 852 (by decide) (by decide) (by decide) a htmp
  have ht : (QueryTupleVisitor.overwriteState 69 852 a).stacks 841 = [] :=
    (QueryTupleVisitor.overwriteState_frame _ _ (by decide) _ _ (by decide)).trans htmp
  have h2 := QueryTupleVisitor.overwrite_eval 703 869 (by decide) (by decide) (by decide)
    (QueryTupleVisitor.overwriteState 69 852 a) ht
  have h869 := QueryTupleVisitor.overwriteState_frame 69 852 (by decide) a 869 (by decide)
  have h703 := QueryTupleVisitor.overwriteState_frame 69 852 (by decide) a 703 (by decide)
  have he := h1.seq (h2.seq (clear_eval lowPorts (copied a)))
  simpa only [finish, finishCost, finished, copied, h869, h703] using he

theorem finished_stacks (a : Data) (i : Fin 896) :
    (finished a).stacks i = if i ∈ lowPorts then [] else
      if i = 869 then a.stacks 703 else if i = 852 then a.stacks 69 else a.stacks i := by
  rw [finished, cleared_stacks, copied,
    QueryTupleVisitor.overwriteState_stacks 703 869 (by decide),
    QueryTupleVisitor.overwriteState_stacks 69 852 (by decide)]
  simp only [Function.update_of_ne (by decide : (703 : Fin 896) ≠ 852)]
  simp only [Function.update_apply]

theorem copied_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (copied a) :=
  QueryTupleVisitor.overwriteState_bound 703 869 (by decide) _ B
    (QueryTupleVisitor.overwriteState_bound 69 852 (by decide) a B ha)

theorem finished_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (finished a) := cleared_bound lowPorts _ B (copied_bound a B ha)

theorem finishCost_le (a : Data) (B : ℕ) (ha : WordBound B a) :
    finishCost a ≤ 130 * B + 185 := by
  have hc := clearCost_le lowPorts (copied a) B (copied_bound a B ha)
  have h1 := ha 852
  have h2 := ha 69
  have h3 := ha 869
  have h4 := ha 703
  rw [show lowPorts.length = 56 by simp [lowPorts]] at hc
  unfold finishCost
  omega

def command : Code := .seq (clearBank entryPorts)
  (.seq FactorAssignmentProgram.setup finish)

def program := compiled command 128 852

/-- Exact changed ports; every other caller word, including tuple and node
controllers, is retained byte for byte. -/
def changed : List (Fin 896) := entryPorts ++
  FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack ++ [852, 869]


structure Initialized (a b : Data) {n width d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word width) d) (u J : ℕ) : Prop where
  unit : b.stacks 852 = MomentsProgram.Product.bytes (FactorAssignmentProgram.oneEntries (n:=n) one)
  unit_good : NativeSemantics.Good (∅ : Finset (Fin n)) u J (FactorAssignmentProgram.oneEntries one)
  baseline : b.stacks 869 = a.stacks 703
  low : ∀ i : Fin 56, b.stacks (i.castAdd 840) = []
  scratch : b.stacks 841 = []
  frame : ∀ i, i ∉ changed → b.stacks i = a.stacks i

/-- One actual initialization constructs its unit and restores the semantic
caller envelope. Physical masters are bounded independently, so the same
bound can be reused for every attained tuple. -/
theorem command_run (a : Data) {n width d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word width) d) (u J P B : ℕ)
    (hu : 0 < u) (hJ : 0 < J)
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one)
    (ha : WordBound B a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      (a.stacks (FactorAssignmentProgram.lowStack p.1)).length ≤ P)
    (hnP : (a.stacks 128).length ≤ P) (hoP : (a.stacks 207).length ≤ P)
    (hPB : 4 * P + 6 ≤ B) :
    ∃ steps b, Eval command steps a b ∧ Initialized a b (n:=n) one u J ∧
      WordBound B b ∧ steps ≤ 1500 * (B + 1) := by
  let start := cleared entryPorts a
  have hstart : WordBound B start := cleared_bound entryPorts a B ha
  have hframe (i : Fin 896) (hi : i ∉ entryPorts) : start.stacks i = a.stacks i := by
    exact (cleared_stacks entryPorts a i).trans (ite_eq_right hi)
  have hlow : ∀ i : Fin 56, start.stacks (i.castAdd 840) = [] := by
    intro i
    rw [cleared_stacks, ite_eq_left]
    exact List.mem_append_left _ ((mem_lowPorts _).mpr i.isLt)
  have h128 := hframe 128 (by decide)
  have h207 := hframe 207 (by decide)
  obtain ⟨b, he, _, hunit, hgood, hcache⟩ := FactorAssignmentProgram.setup_context start one u J
    hu hJ hlow (by simpa only [h128] using hn) (h207.trans ho)
  have hmaster : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      FactorAssignmentProgram.lowStack p.1 ∉ entryPorts := by
    intro p hp
    simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have hcopy' : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      (start.stacks (FactorAssignmentProgram.lowStack p.1)).length ≤ P := by
    intro p hp
    rw [hframe _ (hmaster p hp)]
    exact hcopy p hp
  obtain ⟨c, hc, hbound, _⟩ := FactorAssignmentProgram.setup_eval_wordBound_max start B P hstart
    hcopy' (by simpa only [h128] using hnP) (by simpa only [h207] using hoP)
  have hbc := Eval.final_unique (128 : Fin 896) he hc
  have hb : WordBound B b := by
    rw [hbc]
    simpa only [max_eq_left hPB] using hbound
  have htmp : b.stacks 841 = [] := by
    rw [hcache 841 (by decide)]
    exact (cleared_stacks entryPorts a 841).trans (ite_eq_left (by decide))
  have hwhole := (clear_eval entryPorts a).seq (he.seq (finish_eval b htmp))
  refine ⟨_, finished b, hwhole, ?_, finished_bound b B hb, ?_⟩
  · constructor
    · rw [finished_stacks, ite_eq_right (by decide : (852 : Fin 896) ∉ lowPorts),
        ite_eq_right (by decide : (852 : Fin 896) ≠ 869), ite_eq_left rfl]
      exact hunit
    · exact hgood
    · rw [finished_stacks, ite_eq_right (by decide : (869 : Fin 896) ∉ lowPorts),
        ite_eq_left rfl,
        hcache 703 (by decide), hframe 703 (by decide)]
    · intro i
      rw [finished_stacks, ite_eq_left ((mem_lowPorts _).mpr i.isLt)]
    · rw [finished_stacks, ite_eq_right (by decide : (841 : Fin 896) ∉ lowPorts),
        ite_eq_right (by decide : (841 : Fin 896) ≠ 869),
        ite_eq_right (by decide : (841 : Fin 896) ≠ 852)]
      exact htmp
    · intro i hi
      have hin : i ∉ entryPorts := fun h => hi (List.mem_append_left _ (List.mem_append_left _ h))
      have hcn : i ∉ FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack :=
        fun h => hi (List.mem_append_left _ (List.mem_append_right _ h))
      have h852 : i ≠ 852 := by
        intro h; subst i; exact hi (List.mem_append_right _ (by simp))
      have h869 : i ≠ 869 := by
        intro h; subst i; exact hi (List.mem_append_right _ (by simp))
      have hlo : i ∉ lowPorts := fun h => hin (List.mem_append_left _ h)
      rw [finished_stacks, ite_eq_right hlo, ite_eq_right h869, ite_eq_right h852,
        hcache i hcn, hframe i hin]
  · have hentry := clearCost_le entryPorts a B ha
    have hsetup := FactorAssignmentProgram.setupCost_le start B hstart
    have hfinish := finishCost_le b B hb
    rw [show entryPorts.length = 57 by simp [entryPorts, lowPorts]] at hentry
    omega

/-- The same initialized state is reached on a source trace whose complete
prefix allocation includes every retained caller word and every local step.
The transient polynomial is separate from the compact endpoint bound. -/
theorem program_run_space (a : Data) {n width d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word width) d) (u J P B : ℕ)
    (hu : 0 < u) (hJ : 0 < J)
    (hn : (a.stacks 128).length = n) (ho : a.stacks 207 = RingProgram.flat one)
    (ha : WordBound B a)
    (hcopy : ∀ p ∈ LeafNodeCacheProgram.directCopies,
      (a.stacks (FactorAssignmentProgram.lowStack p.1)).length ≤ P)
    (hnP : (a.stacks 128).length ≤ P) (hoP : (a.stacks 207).length ≤ P)
    (hPB : 4 * P + 6 ≤ B) :
    ∃ steps b, Trace program steps (a.withPC (some program.entry)) (b.withPC none) ∧
      Initialized a b (n:=n) one u J ∧ WordBound B b ∧ steps ≤ 1501 * (B + 1) ∧
      ∀ q z, q ≤ steps → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 2397 * (B + 1) := by
  obtain ⟨steps, b, he, hi, hb, ht⟩ := command_run a one u J P B hu hJ hn ho ha hcopy hnP hoP hPB
  refine ⟨steps + 1, b, compiled_halt_trace he 128 852, hi, hb, by omega, ?_⟩
  have hin : dataBits (a.withPC (some program.entry)) ≤ 896 * B :=
    StreamResources.dataBits_le_mul _ ha
  intro q z hq hz i
  have hg := StructuredSpace.local_stack_bound program (steps := steps + 1) hin q z hq hz i
  omega


open CommandRegisterFrames

/-- Caller flags above the sixteen-register cache bank survive every actual
prefix, including all guarded calls and clearing steps. -/
theorem command_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes command := by
  have hout : ¬ ∃ j, FactorAssignmentProgram.localRegister j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    have := j.isLt
    omega
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have hclear (ports : List (Fin 896)) : i ∉ writes (clearBank ports) :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have hsetup : i ∉ writes FactorAssignmentProgram.setup :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have union_not_mem {s t : Finset (Fin 40)} (hs : i ∉ s) (ht : i ∉ t) : i ∉ s ∪ t := by
    simpa only [Finset.mem_union, not_or] using And.intro hs ht
  have hoverwrite (src dst : Fin 896) : i ∉ writes (QueryTupleVisitor.overwrite src dst) :=
    union_not_mem (not_mem_clearProgram dst 0 1 i h0 h1)
      (not_mem_copyProgram src dst 841 0 1 i h0 h1)
  exact union_not_mem (hclear entryPorts)
    (union_not_mem hsetup (union_not_mem (hoverwrite 69 852)
      (union_not_mem (hoverwrite 703 869) (hclear lowPorts))))

theorem command_register_frame {steps : ℕ} {a b : Data}
    (he : Eval command steps a b) (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  eval_register_frame he i (command_not_mem_writes i hi)

theorem program_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size command + 1)}
    (he : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  compiled_trace_register_frame command 128 852 he i (command_not_mem_writes i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
