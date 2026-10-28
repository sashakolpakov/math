import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLayoutMasters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def stackMap : Fin 768 → Fin 896 := Fin.castAdd 128

def clearPorts : List (Fin 896) :=
  [684,660,665] ++ LayoutMasters.lowPorts.map stackMap

def prepare : Code := liftCommand (clearMany clearPorts) 730 128 registers id

noncomputable def prepared (a : Data) : Data :=
  embedState registers id a
    (clearManyState clearPorts (projectState registers id a))

def prepareCost (a : Data) : ℕ :=
  clearManyCost clearPorts (projectState registers id a)+1

noncomputable def source (a : Data) : State 40 768 :=
  projectState id stackMap (prepared a)

noncomputable def loaded (a : Data) : State 40 768 :=
  embedState LayoutMasters.registers id (source a)
    (LayoutMasters.loaded (LayoutMasters.project (source a)))

def command : Code := .seq prepare
  (liftCommand LayoutMasters.load 730 128 id stackMap)

def program := compiled command 730 128

noncomputable def result (a : Data) : Data :=
  embedState id stackMap (prepared a) (loaded a)

noncomputable def cost (a : Data) : ℕ :=
  prepareCost a+LayoutMasters.loadCost (LayoutMasters.project (source a))+2

theorem prepared_stack (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i ∈ clearPorts then [] else a.stacks i := by
  calc
    _ = (clearManyState clearPorts (projectState registers id a)).stacks i :=
      embedState_stack registers id a _ Function.injective_id i
    _ = _ := clearMany_stacks clearPorts (projectState registers id a) i

theorem prepared_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (prepared a) := by
  intro i
  rw [prepared_stack]
  split_ifs
  · simp
  · exact ha i

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) :=
  eval_liftCommand_from_state (clearMany clearPorts) 730 128 registers id a
    (Fin.castAdd_injective _ _) Function.injective_id
    (clearMany_eval clearPorts (projectState registers id a))

theorem mem_low_clear (i : Fin 14) : stackMap (LayoutMasters.low i) ∈ clearPorts := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨LayoutMasters.low i,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩,rfl⟩

theorem not_mem_high_clear (i : Fin 14) : stackMap (LayoutMasters.high i) ∉ clearPorts := by
  intro h
  rcases List.mem_append.mp h with h|h
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with h|h|h <;> have hv := congrArg Fin.val h <;>
      simp only [stackMap,LayoutMasters.high,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hv <;> omega
  · obtain ⟨j,hj,hj'⟩ := List.mem_map.mp h
    obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
    subst j
    have hv := congrArg Fin.val hj'
    change 128+k.val=730+i.val at hv
    omega

theorem loaded_stack (a : Data) (i : Fin 768) :
    (loaded a).stacks i =
      (LayoutMasters.loaded (LayoutMasters.project (source a))).stacks i := by
  exact embedState_stack _ _ _ _ Function.injective_id i

theorem result_stack (a : Data) (i : Fin 768) :
    (result a).stacks (stackMap i) = (loaded a).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective _ _) i

theorem result_low (a : Data) (i : Fin 14) :
    (result a).stacks (stackMap (LayoutMasters.low i)) =
      a.stacks (stackMap (LayoutMasters.high i)) := by
  rw [result_stack,loaded_stack,LayoutMasters.loaded_low]
  · exact (prepared_stack a _).trans (ite_eq_right (not_mem_high_clear i))
  · intro j
    exact (prepared_stack a _).trans (ite_eq_left (mem_low_clear j))

/-- In particular the addressed plan stream is copied without reindexing. -/
theorem result_plans (a : Data) : (result a).stacks 136=a.stacks 738 :=
  result_low a 8

theorem result_frame (a : Data) (i : Fin 896) (hi : i ∉ clearPorts) :
    (result a).stacks i = a.stacks i := by
  by_cases hlt : i.val<768
  · let j : Fin 768 := ⟨i.val,hlt⟩
    have hj : stackMap j=i := Fin.ext rfl
    have hn : j ∉ LayoutMasters.lowPorts := by
      intro h
      exact hi (List.mem_append_right _ (List.mem_map.mpr ⟨j,h,hj⟩))
    rw [←hj,result_stack,loaded_stack,LayoutMasters.loaded_frame _ _ hn]
    exact (prepared_stack a _).trans (ite_eq_right (by simpa only [hj] using hi))
  · rw [result,embedState_stack_frame]
    · exact (prepared_stack a i).trans (ite_eq_right hi)
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change j.val=i.val at hv
      omega

theorem result_empty (a : Data) (i : Fin 768)
    (hi : i ∈ ([684,660,665] : List (Fin 768))) :
    (result a).stacks (stackMap i)=[] := by
  have hn : i ∉ LayoutMasters.lowPorts := by
    intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 128+j.val=i.val at hv
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> omega
  rw [result_stack,loaded_stack,LayoutMasters.loaded_frame _ _ hn]
  apply (prepared_stack a _).trans
  apply ite_eq_left
  apply List.mem_append_left
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl <;> decide

theorem result_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (result a) := by
  intro i
  by_cases he : ∃ j : Fin 14,stackMap (LayoutMasters.low j)=i
  · obtain ⟨j,rfl⟩ := he
    rw [result_low]
    exact ha _
  by_cases hc : i ∈ clearPorts
  · rcases List.mem_append.mp hc with hc|hc
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl
      · change ((result a).stacks (stackMap 684)).length ≤ B
        rw [result_empty a 684 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 660)).length ≤ B
        rw [result_empty a 660 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 665)).length ≤ B
        rw [result_empty a 665 (by decide)]
        exact Nat.zero_le B
    · obtain ⟨j,hj,hij⟩ := List.mem_map.mp hc
      obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
      exact False.elim (he ⟨k,hk ▸ hij⟩)
  · rw [result_frame a i hc]
    exact ha i

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  have hz : (source a).stacks 684=[] :=
    (prepared_stack a 684).trans (ite_eq_left (by decide))
  have hlocal := LayoutMasters.load_local_eval (LayoutMasters.project (source a)) hz
  have hload : Eval LayoutMasters.load
      (LayoutMasters.loadCost (LayoutMasters.project (source a))+1) (source a) (loaded a) :=
    eval_call_from_state (compiled LayoutMasters.loadLocal 730 128)
      LayoutMasters.registers id (source a) (Fin.castAdd_injective _ _)
      Function.injective_id (compiled_halt_trace hlocal 730 128)
  have hwide := eval_liftCommand_from_state LayoutMasters.load 730 128 id stackMap (prepared a)
    Function.injective_id (Fin.castAdd_injective _ _) hload
  simpa only [command,cost,result,Nat.add_assoc,Nat.reduceAdd] using
    (prepare_eval a).seq hwide

theorem cost_le (a : Data) (B : ℕ) (ha : WordBound B a) : cost a+1 ≤ 132*B+125 := by
  have hp := clearManyCost_le clearPorts (projectState registers id a) B ha
  have hl := LayoutMasters.loadCost_le (LayoutMasters.project (source a)) B
    (fun i => prepared_bound a B ha (stackMap (LayoutMasters.high i)))
  have hn : clearPorts.length=17 := by decide
  rw [hn] at hp
  unfold cost prepareCost
  omega

theorem run_space (a : Data) (B : ℕ) (ha : WordBound B a) :
    ∃ steps,steps ≤ 132*B+125 ∧
      Trace program steps (a.withPC (some program.entry)) ((result a).withPC none) ∧
      WordBound B (result a) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ 1028*B+125 := by
  refine ⟨cost a+1,cost_le a B ha,compiled_halt_trace (command_eval a) 730 128,
    result_bound a B ha,?_⟩
  have hb : dataBits (a.withPC (some program.entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ ha
  intro prefixSteps intermediate hp ht
  have hg := trace_dataBits program ht
  have hc := cost_le a B ha
  omega

theorem command_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ CommandRegisterFrames.writes command := by
  have hn : ¬∃j : Fin 16,registers j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have hp : i ∉ CommandRegisterFrames.writes prepare :=
    CommandRegisterFrames.not_mem_liftCommand _ _ _ _ _ i hn
  have hl : i ∉ CommandRegisterFrames.writes LayoutMasters.load :=
    CommandRegisterFrames.not_mem_liftProgram _ _ _ i hn
  have hw : i ∉ CommandRegisterFrames.writes
      (liftCommand LayoutMasters.load 730 128 id stackMap) := by
    apply CommandRegisterFrames.not_mem_liftCommand_of
    intro j hj
    change j=i at hj
    subst j
    exact hl
  simpa only [command,CommandRegisterFrames.writes,Finset.mem_union,not_or] using
    And.intro hp hw

theorem result_register_frame (a : Data) (i : Fin 40) (hi : 16 ≤ i.val) :
    (result a).regs i=a.regs i :=
  CommandRegisterFrames.eval_register_frame (command_eval a) i
    (command_not_mem_writes i hi)

theorem trace_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size command+1)}
    (ht : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i=a.regs i :=
  CommandRegisterFrames.compiled_trace_register_frame _ _ _ ht i
    (command_not_mem_writes i hi)

/-- All fields name actual parked words or the retained live node counter. -/
structure SourceBank (s : Native.Inputs) (a : Data) : Prop where
  ambient : a.stacks 730=unary s.n
  factors : a.stacks 731=unary s.N
  colors : a.stacks 732=unary s.r
  nodes : a.stacks 733=unary s.Q
  wordWidth : a.stacks 734=unary (s.Q*s.r)
  words : a.stacks 735=s.rows.flatten
  low : a.stacks 736=s.low
  metadata : a.stacks 737=s.metadata
  plans : a.stacks 738=LayoutOwnerFiberProgram.stream s.plans
  order : a.stacks 740=unary s.R
  height : a.stacks 741=s.height
  width : a.stacks 742=s.width
  offset : BinaryArithmetic.toNat (a.stacks 743)=s.offset
  node : a.stacks 307=unary s.node.val

theorem result_ready (s : Native.Inputs) (a : Data) (h : SourceBank s a) :
    Native.Ready s (projectState registers stackMap (result a)) := by
  constructor
  · exact (result_low a 0).trans h.ambient
  · exact (result_low a 1).trans h.factors
  · exact (result_low a 2).trans h.colors
  · exact (result_low a 3).trans h.nodes
  · exact (result_low a 4).trans h.wordWidth
  · exact (result_low a 5).trans h.words
  · exact (result_low a 6).trans h.low
  · exact (result_low a 7).trans h.metadata
  · exact (result_low a 8).trans h.plans
  · exact (result_low a 10).trans h.order
  · exact (result_low a 11).trans h.height
  · exact (result_low a 12).trans h.width
  · exact (congrArg BinaryArithmetic.toNat (result_low a 13)).trans h.offset
  · exact (result_frame a 307 (by decide)).trans h.node
  · exact result_empty a 660 (by decide)
  · exact result_empty a 665 (by decide)

/-- Physical source readiness and both resource bounds hold on this same
fixed paid load, with every caller word included in the prefix bound. -/
theorem native_run_space (s : Native.Inputs) (a : Data) (h : SourceBank s a)
    (B : ℕ) (ha : WordBound B a) :
    ∃ steps, steps ≤ 132*B+125 ∧
      Trace program steps (a.withPC (some program.entry)) ((result a).withPC none) ∧
      Native.Ready s (projectState registers stackMap (result a)) ∧
      WordBound B (result a) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ 1028*B+125 := by
  obtain ⟨steps,ht,hr,hB,hp⟩ := run_space a B ha
  exact ⟨steps,ht,hr,result_ready s a h,hB,hp⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
