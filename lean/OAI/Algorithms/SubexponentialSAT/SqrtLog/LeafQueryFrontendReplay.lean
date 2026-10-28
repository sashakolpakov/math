import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

namespace OAI.Algorithms

/-! The actual frontend neither reads nor writes outer carried tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Replay
open LeafProgram.OuterCarried

private theorem visible (i : Fin 768) (hi : i.val < 320 ∨ 332 < i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false]
  rintro (rfl|rfl|rfl) <;> norm_num at hi

private theorem block_visible (b n : ℕ) (h : b+n ≤ 768) (hb : 332 < b) (i : Fin n) :
    ¬ LeafProgram.OuterCarried.hidden (block b n h i) := by
  apply visible
  right
  dsimp [block]
  omega

private theorem copy_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (copy s d) :=
  avoids_copyProgram LeafProgram.OuterCarried.hidden s d 679 0 1 hs hd (by decide)

private theorem copies_avoids (xs : List (Fin 768 × Fin 768))
    (h : ∀ p∈xs, ¬ LeafProgram.OuterCarried.hidden p.1 ∧ ¬ LeafProgram.OuterCarried.hidden p.2) : AvoidsCmd LeafProgram.OuterCarried.hidden (copies xs) := by
  induction xs with
  | nil => trivial
  | cons p ps ih => exact ⟨copy_avoids p.1 p.2 (h p (by simp)).1 (h p (by simp)).2,
      ih (fun q hq => h q (by simp [hq]))⟩

private theorem sequence_avoids (cs : List Code)
    (h : ∀ c∈cs, AvoidsCmd LeafProgram.OuterCarried.hidden c) : AvoidsCmd LeafProgram.OuterCarried.hidden (sequence cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd]))⟩

private theorem load_avoids (dst : Fin 768) (bits : List Bool) (hd : ¬ LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (loadBits dst bits) := by
  apply avoids_liftProgram
  apply avoids_compiled
  change AvoidsCmd LeafProgram.OuterCarried.hidden (ArithmeticExpressionSupport.pushWord dst bits)
  induction bits with
  | nil => trivial
  | cons b bs ih => exact ⟨ih,trivial,hd⟩

private theorem clear_avoids (ps : List (Fin 768)) (hp : ∀ p∈ps, ¬ LeafProgram.OuterCarried.hidden p) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (BankRoutines.clearCmd 679 (0 : Fin 40) 1 ps) := by
  induction ps with
  | nil => exact avoids_clearProgram LeafProgram.OuterCarried.hidden 679 0 1 (by decide)
  | cons p ps ih => exact ⟨avoids_clearProgram LeafProgram.OuterCarried.hidden p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

private theorem export_field_avoids (f : Exports.Field) (hf : f.Good) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.fieldCommand f) := by
  have hs : ¬ LeafProgram.OuterCarried.hidden f.src := visible _ (Or.inr (by have := hf.1; omega))
  have hd : ¬ LeafProgram.OuterCarried.hidden f.dst := visible _ (by rcases hf.2.2 with h|h; left; omega; right; omega)
  unfold Exports.fieldCommand
  split
  · apply avoids_liftCommand_of_range
    intro i
    unfold Exports.ports
    split
    · exact hs
    · split
      · exact hd
      · apply visible; right; dsimp; omega
  · exact avoids_copyProgram LeafProgram.OuterCarried.hidden f.src f.dst 679 0 1 hs hd (by decide)

private theorem export_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Exports.prepareCommand := by
  refine ⟨?_,?_,clear_avoids _ ?_⟩
  · apply avoids_liftCommand_of_range
    intro i
    apply visible
    right
    dsimp [Exports.bank]
    omega
  · change AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command Exports.fields)
    have h (fs : List Exports.Field) (hf : ∀ f∈fs, f.Good) :
        AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command fs) := by
      induction fs with
      | nil => trivial
      | cons f fs ih => exact ⟨export_field_avoids f (hf f (by simp)),
          ih (fun g hg => hf g (by simp [hg]))⟩
    exact h _ Exports.fields_good
  · intro p hp
    apply visible
    right
    have := (Exports.clearPorts_mem p).mp hp
    omega

private theorem binary_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (binary s d) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> simp [binaryPorts,hs,hd]
  decide

/-- Syntactic avoidance includes peeks, so arbitrary carried words cannot affect time. -/
theorem frontend_avoids (k : ℕ) : AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := by
  have hcount : AvoidsCmd LeafProgram.OuterCarried.hidden countHashes := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hraw : AvoidsCmd LeafProgram.OuterCarried.hidden rawCommand := by
    refine ⟨sequence_avoids _ ?_,?_,copy_avoids _ _ (by decide) (by decide)⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl)
      · apply copies_avoids
        simp [scopeCopies,LeafProgram.OuterCarried.hidden]
      · exact load_avoids _ _ (by decide)
      · simp [resetScopeRegs,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 500 80 _ (by decide))
  have hhigh : AvoidsCmd LeafProgram.OuterCarried.hidden highCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 417 77 _ (by decide))
    · apply copies_avoids
      simp [highCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 580 32 _ (by decide))
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hmeasure : AvoidsCmd LeafProgram.OuterCarried.hidden measureCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · apply copies_avoids
      simp [statsCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 612 21 _ (by decide))
    · apply copies_avoids
      simp [arityCopies,LeafProgram.OuterCarried.hidden]
    · simp [arityRegisters,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 633 12 _ (by decide))
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hnumeric : AvoidsCmd LeafProgram.OuterCarried.hidden (numericStage k) := by
    refine ⟨copies_avoids _ ?_,load_avoids _ _ (by decide),sequence_avoids _ ?_⟩
    · simp [LeafProgram.OuterCarried.hidden]
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl|rfl|rfl) <;> exact binary_avoids _ _ (by decide) (by decide)
  refine ⟨hcount,⟨hraw,hhigh,hmeasure,hnumeric,?_⟩,export_avoids,?_,?_,?_⟩
  · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 340 77 _ (by decide))
  · apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · refine ⟨copy_avoids _ _ (by decide) (by decide),?_⟩
    apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · apply clear_avoids
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact block_visible 417 262 _ (by decide) i

end Replay

/-- The concrete frontend does not read or write tapes 320, 322, or 332. -/
theorem frontend_avoids_outerCarried (k : ℕ) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := Replay.frontend_avoids k

/-- Replacing any outer carried words leaves the actual frontend duration unchanged. -/
theorem frontend_eval_rebase_outerCarried (k : ℕ) {n : ℕ} {a b : Data}
    (h : Eval (frontend k) n a b) (frame : Fin 768 → List Bool) :
    Eval (frontend k) n (rebaseState LeafProgram.OuterCarried.hidden frame a)
      (rebaseState LeafProgram.OuterCarried.hidden frame b) :=
  eval_rebase _ (frontend_avoids_outerCarried k) h frame

#print axioms frontend_avoids_outerCarried
#print axioms frontend_eval_rebase_outerCarried
end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
