import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramMask

namespace OAI.Algorithms

/-! Syntactic footprints for the paid copies and isolated service calls used
by head setup. A local service may access every one of its own tapes: its
entire bank is relocated into the reserved, visible workspace. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage ProgramTapeReplay

theorem avoids_copyMany {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p∈ps,¬ H p.1 ∧ ¬ H p.2) : AvoidsCmd H (copyMany tmp ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_copyProgram H p.1 p.2 tmp 0 1 (hp p (by simp)).1
      (hp p (by simp)).2 ht,ih (fun q hq=>hp q (by simp [hq]))⟩

theorem avoids_clearMany {s : ℕ} (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p∈ps,¬ H p) : AvoidsCmd H (clearMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_clearProgram H p 0 1 (hp p (by simp)),ih (fun q hq=>hp q (by simp [hq]))⟩

theorem avoids_resetMany {s : ℕ} (H : Fin s → Prop) (rs : List (Fin 16)) :
    AvoidsCmd H (resetMany (S:=s) rs) := by
  induction rs with
  | nil => trivial
  | cons r rs ih => exact ⟨trivial,ih⟩

theorem avoids_prepare {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (ins : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (hi : ∀ p∈ins,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (prepare tmp ps ins) :=
  ⟨avoids_clearMany H [tmp] (by simpa using ht),avoids_clearMany H ps hp,
    avoids_resetMany H workRegisters,avoids_copyMany H tmp ins ht hi⟩

theorem avoids_finish {s : ℕ} (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s)) (outs : List (Fin s × Fin s))
    (ht : ¬ H tmp) (hp : ∀ p∈ps,¬ H p) (ho : ∀ p∈outs,¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (finish tmp ps outs) := by
  refine ⟨avoids_clearMany H (outs.map Prod.snd) ?_,avoids_copyMany H tmp outs ht ho,
    avoids_clearMany H ps hp,avoids_resetMany H workRegisters⟩
  intro q hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact (ho p hp).2

theorem work_not_hidden {s : ℕ} (hs : s ≤ 288) (i : Fin s) : ¬ Hidden (workPort hs i) := by
  intro h
  simp only [Hidden,carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with h|h|h|h|h|h|h <;>
    have hv := congrArg Fin.val h <;>
    norm_num [workPort] at hv <;> omega

theorem workPorts_not_hidden {s : ℕ} (hs : s ≤ 288) : ∀ i∈workPorts hs,¬ Hidden i := by
  intro i hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
  exact work_not_hidden hs j

theorem avoids_stage {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s ≤ 288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ Hidden q.1) (ho : ∀ q∈outs,¬ Hidden q.2) :
    AvoidsCmd Hidden (stage p reg hs ins outs) := by
  have ht : ¬ Hidden temporary := by decide
  have hin : ∀ q∈inputCopies hs ins,¬ Hidden q.1 ∧ ¬ Hidden q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨hi z hz,work_not_hidden hs z.2⟩
  have hout : ∀ q∈outputCopies hs outs,¬ Hidden q.1 ∧ ¬ Hidden q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨work_not_hidden hs z.1,ho z hz⟩
  exact ⟨avoids_prepare Hidden temporary (workPorts hs) (inputCopies hs ins)
      ht (workPorts_not_hidden hs) hin,
    avoids_liftProgram_of_range Hidden p reg (workPort hs) (work_not_hidden hs),
    avoids_finish Hidden temporary (workPorts hs) (outputCopies hs outs)
      ht (workPorts_not_hidden hs) hout⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint

end OAI.Algorithms
