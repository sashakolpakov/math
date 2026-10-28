import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionScheduleBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupEnvelope
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpSetupInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Schedule

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

abbrev localProgram := compiled Execution.ScheduleLocal.command (18 : Fin 22) 21

theorem fits (c : Config) : 22 < helperSize c := small_fits c (by decide)
def inputs (c : Config) : List (Fin (stackCount c) × Fin 22) :=
  [(persistent c 2,18),(persistent c 4,21)]
def outputs (c : Config) : List (Fin 22 × Fin (stackCount c)) :=
  [(19,persistent c 30),(20,persistent c 31),(21,persistent c 4)]
def command (c : Config) : SetupCmd c :=
  stage c localProgram (registerPort (by decide : 8 ≤ 9)) (fits c) (inputs c) (outputs c)

noncomputable def start (c : Config) (a : SetupState c) : Execution.ScheduleLocal.Data :=
  project (registerPort (by decide : 8 ≤ 9)) (workPort c (fits c))
    (prepared c (fits c) (inputs c) a)
noncomputable def result (c : Config) (a : SetupState c) (out : Execution.ScheduleLocal.Data) :=
  returned c (registerPort (by decide : 8 ≤ 9)) (fits c) (inputs c) (outputs c) a out
noncomputable def cost (c : Config) (a : SetupState c) (out : Execution.ScheduleLocal.Data) (u : ℕ) :=
  stageCost c (registerPort (by decide : 8 ≤ 9)) (fits c) (inputs c) (outputs c) a out (u+1)

theorem inputs_protected (c : Config) : ∀ p ∈ inputs c, Protected c p.1 := by
  intro p hp
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl <;> exact persistent_protected c _
theorem outputs_protected (c : Config) : ∀ p ∈ outputs c, Protected c p.2 := by
  intro p hp
  simp only [outputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact persistent_protected c _
theorem inputs_nodup (c : Config) : ((inputs c).map Prod.snd).Nodup := by simp [inputs]
theorem outputs_nodup (c : Config) : ((outputs c).map Prod.snd).Nodup := by simp [outputs]

theorem start_word (c : Config) (a : SetupState c) (p : Fin (stackCount c) × Fin 22)
    (hp : p ∈ inputs c) : (start c a).stacks p.2 = a.stacks p.1 :=
  prepared_word c (fits c) (inputs c) a (inputs_protected c) (inputs_nodup c) p hp

theorem start_ready (c : Config) (a : SetupState c) : Execution.ScheduleLocal.Ready (start c a) := by
  have hz (j : Fin 22) (h18 : j ≠ 18) (h21 : j ≠ 21) : (start c a).stacks j = [] := by
    apply prepared_empty c (fits c) (inputs c) a j
    intro p hp
    simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact h18
    · exact h21
  refine ⟨?_,hz 19 (by decide) (by decide),hz 20 (by decide) (by decide)⟩
  intro i
  apply hz
  all_goals intro h; have := congrArg Fin.val h; have := i.isLt; simp only [Fin.val_castLE] at *; omega

theorem call_eval (c : Config) (a : SetupState c) (out : Execution.ScheduleLocal.Data) {u : ℕ}
    (he : Eval Execution.ScheduleLocal.command u (start c a) out) :
    Eval (command c) (cost c a out u) a (result c a out) :=
  stage_eval c localProgram (registerPort (by decide : 8 ≤ 9)) (registerPort_injective (by decide))
    (fits c) (inputs c) (outputs c) a (start c a) out
    (inputs_protected c) (outputs_protected c) rfl (compiled_halt_trace he 18 21)

theorem result_word (c : Config) (a : SetupState c) (out : Execution.ScheduleLocal.Data)
    (p : Fin 22 × Fin (stackCount c)) (hp : p ∈ outputs c) :
    (result c a out).stacks p.2 = out.stacks p.1 :=
  returned_word c (registerPort (by decide : 8 ≤ 9)) (fits c) (inputs c) (outputs c) a out
    (outputs_protected c) (outputs_nodup c) p hp

theorem result_frame (c : Config) (a : SetupState c) (out : Execution.ScheduleLocal.Data)
    (i : Fin 32) (h4 : i ≠ 4) (h30 : i ≠ 30) (h31 : i ≠ 31) :
    (result c a out).stacks (persistent c i) = a.stacks (persistent c i) := by
  apply returned_frame c _ _ _ _ _ _ _ (persistent_protected c i)
  intro p hp
  simp only [outputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simpa using h30
  · simpa using h31
  · simpa using h4

/-- A real isolated call overwrites the new schedule and retains every other
persistent word. The old s word is an input only so its destruction is charged. -/
theorem command_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (command c) t a b ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 30)) =
        Asymptotic.L (BinaryArithmetic.toNat (a.stacks (persistent c 2))) ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 31)) =
        Asymptotic.w (BinaryArithmetic.toNat (a.stacks (persistent c 2))) ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 4)) =
        Asymptotic.s (BinaryArithmetic.toNat (a.stacks (persistent c 2))) ∧
      (∀ i : Fin 32, i ≠ 4 → i ≠ 30 → i ≠ 31 →
        b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨u,out,he,hL,hw,hs,_,_,_,_⟩ := Execution.ScheduleLocal.command_eval (start c a) (start_ready c a)
  have hn := start_word c a (persistent c 2,18) (by simp [inputs])
  have h30 := result_word c a out (19,persistent c 30) (by simp [outputs])
  have h31 := result_word c a out (20,persistent c 31) (by simp [outputs])
  have h4 := result_word c a out (21,persistent c 4) (by simp [outputs])
  simp only [SubexpParameterProgram.value_eq_toNat,hn] at hL hw hs
  exact ⟨cost c a out u,result c a out,call_eval c a out he,
    by simpa only [h30] using hL,by simpa only [h31] using hw,by simpa only [h4] using hs,
    result_frame c a out⟩

end SubexponentialSAT.SqrtLog.Setup.Schedule

end OAI.Algorithms
