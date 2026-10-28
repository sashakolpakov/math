import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

/-! The actual key and paid head preparation never inspect or modify the
pending caller word320 or accumulated count322, including through peeks. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HighQueryAdapter

theorem bank_clear_avoids {r s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (value present : Fin r) (ports : List (Fin s)) (ht : ¬ H tmp)
    (hp : ∀ i ∈ ports, ¬ H i) :
    AvoidsCmd H (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram H tmp value present ht
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i value present (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

theorem key_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureKeyNative.command := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem key_machine_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureKeyNative.machine := key_avoids

theorem reset_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.reset := by
  refine ⟨avoids_clearProgram _ 841 0 1 (by decide),
    bank_clear_avoids _ 841 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [SignatureHeadPrepare.cleared, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem overwrite_avoids (H : Fin 896 → Prop) (src dst : Fin 896)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H 841) :
    AvoidsCmd H (QueryTupleVisitor.overwrite src dst) :=
  ⟨avoids_clearProgram H dst 0 1 hd, avoids_copyProgram H src dst 841 0 1 hs hd ht⟩

theorem masters_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.masters :=
  ⟨overwrite_avoids _ 141 864 (by decide) (by decide) (by decide),
    overwrite_avoids _ 847 865 (by decide) (by decide) (by decide),
    overwrite_avoids _ 671 175 (by decide) (by decide) (by decide)⟩

theorem select_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.select := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem selector_command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.command :=
  ⟨avoids_copyProgram _ 858 878 880 0 1 (by decide) (by decide) (by decide),
    avoids_copyProgram _ 670 879 880 0 1 (by decide) (by decide) (by decide),
    select_avoids⟩

theorem selector_reset_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.reset := by
  refine ⟨avoids_clearProgram _ 880 0 1 (by decide),
    bank_clear_avoids _ 880 0 1 _ (by decide) ?_⟩
  intro i hi
  simp only [NativeHeadSelect.changed, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem selector_prepare_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.prepare := ⟨selector_reset_avoids, selector_command_avoids⟩

theorem selector_program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      NativeHeadSelect.prepareProgram :=
  avoids_compiled _ _ selector_prepare_avoids 858 867

theorem command_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.command :=
  ⟨reset_avoids, key_avoids, masters_avoids, selector_program_avoids⟩

theorem program_avoids :
    AvoidsProgram (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      SignatureHeadPrepare.program :=
  avoids_compiled _ _ command_avoids 838 866

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepareFootprint
