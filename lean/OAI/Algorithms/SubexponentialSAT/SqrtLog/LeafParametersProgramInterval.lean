import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramCacheWidth
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalStartProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalStart

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem intervalStart_le_product (r Q R : ℕ) (hr : 0 < r) :
    Subexp.TailInterval.intervalStart r Q R ≤ Q*r := by
  rw [← SubexpIntervalStart.value_eq_intervalStart r Q R hr]
  exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans
    (Nat.mul_le_mul (Nat.sub_le Q 1) (Nat.sub_le r 1)))

theorem cacheWidth_le (r Q R : ℕ) (hr : 0 < r) :
    1+2*Subexp.TailInterval.intervalStart r Q R*R+Q ≤ 1+2*(Q*r)*R+Q := by
  gcongr
  exact intervalStart_le_product r Q R hr

/-- The preserving interval routine can read the parameter words directly.
Its private work bank is cleared by the preceding finite instruction table. -/
def ports : Fin 32 → Fin 77 :=
  ![18,21,29,46,47,48,49,50,51,52,53,54,55,56,57,58,
    59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74]

theorem ports_injective : Function.Injective ports := by decide

def prepare : List Instr := [
  .clear 46,.clear 47,.clear 48,.clear 49,.clear 50,.clear 51,
  .clear 52,.clear 53,.clear 54,.clear 55,.clear 56,.clear 57,
  .clear 58,.clear 59,.clear 60,.clear 61,.clear 62,.clear 63]

abbrev intervalAt : Cmd 8 77 :=
  .call (ProgramLinking.liftProgram SubexpIntervalStartProgram.program id ports)

private theorem project_initial (r : Regs) (w : Words)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[]) :
    projectState id ports (Bank.state r w)=
      SubexpIntervalStartProgram.initialState r (w 18) (w 21) (w 29) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [ports,Bank.state,
        SubexpIntervalCoreProgram.inputWords]
    all_goals apply hc; decide

private theorem embed_final (r rf : Regs) (w : Words) (word : List Bool)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[]) :
    embedState id ports (Bank.state r w)
      (SubexpIntervalStartProgram.finalState rf (w 18) (w 21) (w 29) word)=
        Bank.state rf (Function.update w 46 word) := by
  apply embedState_eq_of_ports id ports (Bank.state r w) _ _
    Function.injective_id ports_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [ports,Bank.state,SubexpIntervalStartProgram.finalState,
        SubexpIntervalCoreProgram.state,SubexpIntervalCoreProgram.inputWords]
    all_goals apply hc; decide
  · intro i hi
    have ho : i≠Bank.port 46 := by
      intro he
      exact hi ⟨3,by simpa [ports,Bank.port] using he.symm⟩
    rw [← Bank.state_update r rf w 46 word]
    simp only [Function.update_of_ne ho]

theorem at_eval (r : Regs) (w : Words)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[])
    (hr : 0 < BinaryArithmetic.toNat (w 18)) :
    ∃ t rf word, Eval intervalAt t (Bank.state r w)
        (Bank.state rf (Function.update w 46 word)) ∧
      BinaryArithmetic.toNat word=Subexp.TailInterval.intervalStart
        (BinaryArithmetic.toNat (w 18)) (BinaryArithmetic.toNat (w 21)) (BinaryArithmetic.toNat (w 29)) ∧
      word.length ≤ 4*((w 18).length+(w 21).length+(w 29).length+1) ∧
      t ≤ 10000*((w 18).length+(w 21).length+(w 29).length+1)^2+1 := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := SubexpIntervalStartProgram.command_eval
    r (w 18) (w 21) (w 29) hr
  have hp := project_initial r w hc
  have htrace := compiled_halt_trace he (0 : Fin 32) 3
  rw [← hp] at htrace
  have hh := eval_call_from_state SubexpIntervalStartProgram.program id ports
    (Bank.state r w) Function.injective_id ports_injective htrace
  rw [embed_final r rf w word hc] at hh
  refine ⟨t+1,rf,word,hh,?_,hl,Nat.add_le_add_right ht 1⟩
  exact hv.trans (SubexpIntervalStart.value_eq_intervalStart _ _ _ hr)

theorem prepare_admissible (m : Model) : AdmissibleCode prepare m := by
  simp [prepare,AdmissibleCode,Admissible]

theorem prepare_empty (m : Model) (w : Words) (hs : Shape (result prepare m) w)
    (a : Fin 64) (ha : 46 ≤ a.val) : w a=[] := by
  have hl := hs.2 a
  fin_cases a <;> simp_all [prepare,result,next,output,lengthBound]

theorem prepare_frame (m : Model) (a : Fin 64) (ha : a.val < 46) :
    (result prepare m).val a=m.val a ∧ (result prepare m).len a=m.len a := by
  have hne (k : Fin 64) (hk : 46 ≤ k.val) : a≠k := by
    intro he; subst k; omega
  simp [prepare,result,next,output,lengthBound,hne _ (by decide : 46 ≤ (46 : Fin 64).val),
    hne _ (by decide : 46 ≤ (47 : Fin 64).val),hne _ (by decide : 46 ≤ (48 : Fin 64).val),
    hne _ (by decide : 46 ≤ (49 : Fin 64).val),hne _ (by decide : 46 ≤ (50 : Fin 64).val),
    hne _ (by decide : 46 ≤ (51 : Fin 64).val),hne _ (by decide : 46 ≤ (52 : Fin 64).val),
    hne _ (by decide : 46 ≤ (53 : Fin 64).val),hne _ (by decide : 46 ≤ (54 : Fin 64).val),
    hne _ (by decide : 46 ≤ (55 : Fin 64).val),hne _ (by decide : 46 ≤ (56 : Fin 64).val),
    hne _ (by decide : 46 ≤ (57 : Fin 64).val),hne _ (by decide : 46 ≤ (58 : Fin 64).val),
    hne _ (by decide : 46 ≤ (59 : Fin 64).val),hne _ (by decide : 46 ≤ (60 : Fin 64).val),
    hne _ (by decide : 46 ≤ (61 : Fin 64).val),hne _ (by decide : 46 ≤ (62 : Fin 64).val),
    hne _ (by decide : 46 ≤ (63 : Fin 64).val)]

def intervalModel (m : Model) : Model :=
  let p := result prepare m
  { val := Function.update p.val 46
      (Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29))
    len := Function.update p.len 46 (4*(m.len 18+m.len 21+m.len 29+1)) }

abbrev command : Cmd 8 77 :=
  .seq (Circuit.program prepare) (.seq intervalAt CacheWidth.command)

def finalModel (m : Model) : Model := result CacheWidth.code (intervalModel m)

theorem intervalModel_input (m : Model) (a : Fin 64) (ha : a.val < 46) :
    (intervalModel m).val a=m.val a := by
  have hne : a≠46 := by intro h; subst a; contradiction
  simpa [intervalModel,hne] using (prepare_frame m a ha).1

theorem final_values (m : Model) :
    (finalModel m).val 29=m.val 29 ∧
    (finalModel m).val 46=Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29) ∧
    (finalModel m).val 47=m.val 21*m.val 18 ∧
    (finalModel m).val 50=1+2*
      Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21 := by
  have hi (a : Fin 64) (ha : a.val < 46) := intervalModel_input m a ha
  have hA : (intervalModel m).val 46=
      Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29) := by
    simp [intervalModel]
  have hv := CacheWidth.values (intervalModel m)
  refine ⟨?_,?_,?_,?_⟩
  · exact (CacheWidth.frame (intervalModel m) 29 (by decide) (by decide)
      (by decide) (by decide)).trans (hi 29 (by decide))
  · exact (CacheWidth.frame (intervalModel m) 46 (by decide) (by decide)
      (by decide) (by decide)).trans hA
  · simpa only [finalModel,hi 21 (by decide),hi 18 (by decide)] using hv.1
  · simpa only [finalModel,hA,hi 29 (by decide),hi 21 (by decide)] using hv.2

def runtimeBound (m : Model) : ℕ :=
  budget prepare m+10000*(m.len 18+m.len 21+m.len 29+1)^2+1+
    budget CacheWidth.code (intervalModel m)

theorem command_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (finalModel m) w' ∧ t ≤ runtimeBound m := by
  obtain ⟨t1,r1,w1,he1,hs1,ht1⟩ := Circuit.program_eval prepare m w r hs (prepare_admissible m)
  have hval (a : Fin 64) (ha : a.val < 46) : BinaryArithmetic.toNat (w1 a)=m.val a :=
    (hs1.1 a).trans (prepare_frame m a ha).1
  have hlen (a : Fin 64) (ha : a.val < 46) : (w1 a).length ≤ m.len a :=
    (hs1.2 a).trans_eq (prepare_frame m a ha).2
  obtain ⟨t2,r2,v,he2,hv,hl,ht2⟩ := at_eval r1 w1
    (prepare_empty m w1 hs1) (by rw [hval 18 (by decide)]; exact hr)
  let w2 := Function.update w1 46 v
  have hs2 : Shape (intervalModel m) w2 := by
    constructor
    · intro a
      by_cases ha : a=46
      · subst a
        simpa [intervalModel,w2,hval 18 (by decide),hval 21 (by decide),
          hval 29 (by decide)] using hv
      · simpa [intervalModel,w2,ha] using hs1.1 a
    · intro a
      by_cases ha : a=46
      · subst a
        simp only [intervalModel,w2,Function.update_self]
        calc
          v.length ≤ 4*((w1 18).length+(w1 21).length+(w1 29).length+1) := hl
          _ ≤ 4*(m.len 18+m.len 21+m.len 29+1) := by
            gcongr <;> exact hlen _ (by decide)
      · simpa [intervalModel,w2,ha] using hs1.2 a
  obtain ⟨t3,r3,w3,he3,hs3,ht3⟩ := CacheWidth.command_eval (intervalModel m) w2 r2 hs2
  have htime : t2 ≤ 10000*(m.len 18+m.len 21+m.len 29+1)^2+1 := by
    apply ht2.trans
    gcongr <;> exact hlen _ (by decide)
  exact ⟨t1+(t2+t3),r3,w3,he1.seq (he2.seq he3),hs3,by dsimp [runtimeBound]; omega⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
