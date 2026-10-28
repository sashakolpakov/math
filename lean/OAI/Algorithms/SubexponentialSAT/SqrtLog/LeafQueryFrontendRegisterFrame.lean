import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRegisterSafety

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls RegisterSafety
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
attribute [local irreducible] clearPrivate

private theorem outside (j : Fin 40) (hj : 11 ≤ j.val) (n : ℕ) (hn : n ≤ 11)
    (hn' : n ≤ 40) (i : Fin n) : j≠registers n hn' i := by
  intro h
  have := congrArg Fin.val h
  dsimp [registers] at this
  omega

private theorem copies_safe (j : Fin 40) (hj : 11 ≤ j.val)
    (xs : List (Fin 768 × Fin 768)) : safe j (copies xs) := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨copy_safe _ _ _ _ _ _ h0 h1,ih⟩

private theorem clearPrivate_safe (j : Fin 40) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    safe j (BankRoutines.clearCmd 679 (0 : Fin 40) 1
      ((List.finRange 262).map (block 417 262 (by decide)))) :=
  clearCmd_safe 679 0 1 j h0 h1 _

private theorem sequence_safe (j : Fin 40) (xs : List Code)
    (h : ∀ c∈xs, safe j c) : safe j (sequence xs) := by
  induction xs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c List.mem_cons_self,ih (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

private theorem export_safe (j : Fin 40) (hj : 11 ≤ j.val) : safe j Exports.prepareCommand := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  refine ⟨?_,?_,clearCmd_safe _ _ _ _ h0 h1 _⟩
  · apply liftCommand_safe
    intro i h
    have := congrArg Fin.val h
    dsimp [Exports.bankRegs] at this
    omega
  · have hf (f : Exports.Field) : safe j (Exports.fieldCommand f) := by
      unfold Exports.fieldCommand
      split
      · apply liftCommand_safe
        intro i h
        have := congrArg Fin.val h
        dsimp [Exports.regs] at this
        omega
      · exact copy_safe _ _ _ _ _ _ h0 h1
    change safe j (Exports.command Exports.fields)
    generalize Exports.fields=fs
    induction fs with
    | nil => trivial
    | cons f fs ih => exact ⟨hf f,ih⟩

theorem frontend_register_safe (k : ℕ) (j : Fin 40) (hj : 11 ≤ j.val) :
    safe j (frontend k) := by
  have h0 : j≠0 := by intro h; subst j; norm_num at hj
  have h1 : j≠1 := by intro h; subst j; norm_num at hj
  have hc (s d : Fin 768) : safe j (copy s d) := copy_safe _ _ _ _ _ _ h0 h1
  have hl {n s l : ℕ} (hn : n ≤ 11) (hn' : n ≤ 40) (p : Program n s l)
      (ss : Fin s → Fin 768) : safe j (.call (ProgramLinking.liftProgram p (registers n hn') ss)) :=
    lift_safe p _ ss j (outside j hj n hn hn')
  have hb (s : Fin 768) (w : List Bool) : safe j (loadBits s w) :=
    liftCommand_safe _ _ _ _ _ _ (outside j hj 8 (by decide) (by decide))
  have hne (i : Fin 40) (hi : i.val < 11) : j≠i := by
    intro h; subst j; omega
  have hr : safe j resetScopeRegs := by
    simp only [resetScopeRegs,setRegs,SubexpParameterProgram.atoms,safe,baseSafe]
    simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,
      hne 0 (by decide),hne 1 (by decide),hne 2 (by decide),hne 3 (by decide),hne 4 (by decide),hne 5 (by decide),hne 6 (by decide),hne 7 (by decide),hne 8 (by decide),hne 9 (by decide),hne 10 (by decide)]
  have har : safe j arityRegisters := by
    simp only [arityRegisters,setRegs,SubexpParameterProgram.atoms,safe,baseSafe]
    simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,
hne 7 (by decide),hne 8 (by decide),hne 9 (by decide)]
  have hs (cs : List Code) (h : ∀ c∈cs, safe j c) := sequence_safe j cs h
  have hseq {cs : List Code} (h : ∀ c∈cs, safe j c) : safe j (sequence cs) := hs cs h
  have hbin (s d : Fin 768) : safe j (binary s d) := hl (by decide) _ _ _
  have hcount : safe j countHashes := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl
    · exact hc _ _
    · exact hl (by decide) _ _ _
  have hraw : safe j rawCommand := by
    refine ⟨?_,hl (by decide) _ _ _,hc _ _⟩
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl
    · exact copies_safe j hj _
    · exact hb _ _
    · exact hr
  have hhigh : safe j highCommand := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hc _ _
    · exact hl (by decide) _ _ _
    · exact copies_safe j hj _
    · exact hl (by decide) _ _ _
    · exact hc _ _
    · exact hl (by decide) _ _ _
  have hmeasure : safe j measureCommand := by
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact copies_safe j hj _
    · exact hl (by decide) _ _ _
    · exact copies_safe j hj _
    · exact har
    · exact hl (by decide) _ _ _
    · exact hl (by decide) _ _ _
  have hnumeric : safe j (numericStage k) := by
    refine ⟨copies_safe j hj _,hb _ _,?_⟩
    apply hseq
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro c h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> exact hbin _ _
  refine ⟨hcount, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hraw, ?_⟩
    refine ⟨hhigh, ?_⟩
    refine ⟨hmeasure, ?_⟩
    constructor
    · exact hnumeric
    · exact hl (by decide) _ _ _
  · refine ⟨export_safe j hj, ?_⟩
    refine ⟨hl (by decide) _ _ _, ?_⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hc _ _, hl (by decide) _ _ _⟩
    · have heq : clearPrivate = BankRoutines.clearCmd 679 (0 : Fin 40) 1
          ((List.finRange 262).map (block 417 262 (by decide))) := by
        exact clearPrivate_eq
      exact heq.symm ▸ clearPrivate_safe j h0 h1

/-- All parser registers, including 16, 17, and 18, survive the actual native
frontend on both outcomes of its computed guard. -/
theorem frontend_register_frame (k : ℕ) {n : ℕ} {a b : Data}
    (he : Eval (frontend k) n a b) (j : Fin 40) (hj : 11 ≤ j.val) :
    b.regs j=a.regs j := frame he j (frontend_register_safe k j hj)

theorem frontend_parser_registers (k : ℕ) {n : ℕ} {a b : Data}
    (he : Eval (frontend k) n a b) :
    b.regs 16=a.regs 16 ∧ b.regs 17=a.regs 17 ∧ b.regs 18=a.regs 18 :=
  ⟨frontend_register_frame k he 16 (by decide),
    frontend_register_frame k he 17 (by decide),frontend_register_frame k he 18 (by decide)⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
