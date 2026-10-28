import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def Protected (i : Fin 768) : Prop :=
  i=320 ∨ i=322 ∨ i=323 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨ 744 ≤ i.val

instance (i : Fin 768) : Decidable (Protected i) := inferInstanceAs (Decidable
  (i=320 ∨ i=322 ∨ i=323 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨ 744 ≤ i.val))

private opaque cleanupPortsWrapped :
    {ports : List (Fin 768) //
      ports = (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699))} :=
  ⟨(List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)), rfl⟩

/-- The fixed lower-workspace cleanup table, kept opaque so elaboration does
not reduce its 768 candidates while checking unrelated resource proofs. -/
def cleanupPorts : List (Fin 768) := cleanupPortsWrapped.1

theorem cleanupPorts_eq :
    cleanupPorts =
      (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)) :=
  cleanupPortsWrapped.2

@[simp] theorem mem_cleanupPorts (i : Fin 768) :
    i∈cleanupPorts ↔ ¬Protected i ∧ i≠699 := by
  rw [cleanupPorts_eq]
  simp

theorem cleanupPorts_nodup : cleanupPorts.Nodup :=
  cleanupPorts_eq.symm ▸ (List.nodup_finRange 768).filter _

theorem cleanupPorts_length_le : cleanupPorts.length ≤ 768 := by
  rw [cleanupPorts_eq]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := 768))

def cleanup : Code := .seq (.call (StackRoutines.clearProgram 699 0 1))
  (BankRoutines.clearCmd 699 0 1 cleanupPorts)

def cleaned (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks cleanupPorts (Function.update a.stacks 699 [])⟩

def cleanupCost (a : Data) : ℕ :=
  2*(a.stacks 699).length+6+3*cleanupPorts.length+
    2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum

theorem cleanup_eval (a : Data) : Eval cleanup (cleanupCost a) a (cleaned a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,Function.update a.stacks 699 []⟩
  have h1 : Eval (.call (StackRoutines.clearProgram 699 0 1))
      (2*(a.stacks 699).length+3) a mid :=
    Eval.call _ (ListRegisterProgram.clear_run (699 : Fin 768) (0 : Fin 40) 1 a.regs a.stacks)
  have h2 := BankRoutines.clear_eval (699 : Fin 768) (0 : Fin 40) 1 cleanupPorts
    cleanupPorts_nodup mid.regs mid.stacks (by simp [mid])
  have hm : cleanupPorts.map (fun i => (mid.stacks i).length)=
      cleanupPorts.map (fun i => (a.stacks i).length) := by
    apply List.map_congr_left
    intro i hi
    have hn := (mem_cleanupPorts i).mp hi
    simp [mid,hn.2]
  rw [hm] at h2
  have hf : (⟨readRegs mid.regs 0 1 none,
      BankRoutines.clearBankStacks cleanupPorts mid.stacks⟩ : Data)=cleaned a := by
    simp [mid,cleaned,StackRoutines.readRegs_reset]
  rw [hf] at h2
  have he := h1.seq h2
  have hk : (2*(a.stacks 699).length+3)+
      (2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum+3*cleanupPorts.length+3)=
      cleanupCost a := by
    unfold cleanupCost
    omega
  rw [hk] at he
  exact he

theorem cleaned_stacks (a : Data) (i : Fin 768) :
    (cleaned a).stacks i=if Protected i then a.stacks i else [] := by
  by_cases hp : Protected i
  · have hn : i≠699 := by
      intro h
      subst i
      exact (by decide : ¬Protected (699 : Fin 768)) hp
    simp [cleaned,BankRoutines.clearBankStacks,hp,hn]
  · by_cases hn : i=699
    · subst i
      simp [cleaned,BankRoutines.clearBankStacks,show ¬Protected (699 : Fin 768) from by decide]
    · simp [cleaned,BankRoutines.clearBankStacks,hp,hn]

theorem cleaned_frame (a : Data) (i : Fin 768) (hi : Protected i) :
    (cleaned a).stacks i=a.stacks i := by rw [cleaned_stacks,ite_eq_left hi]

theorem cleaned_empty (a : Data) (i : Fin 768) (hi : ¬Protected i) :
    (cleaned a).stacks i=[] := by rw [cleaned_stacks,ite_eq_right hi]

theorem cleaned_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (cleaned a).regs i=a.regs i := by
  apply StackRoutines.readRegs_frame
  · intro h; subst i; simp at hi
  · intro h; subst i; simp at hi

theorem cleaned_parser (a : Data) :
    (cleaned a).regs 16=a.regs 16 ∧ (cleaned a).regs 17=a.regs 17 ∧
      (cleaned a).regs 18=a.regs 18 :=
  ⟨cleaned_register_frame a 16 (by decide),cleaned_register_frame a 17 (by decide),
    cleaned_register_frame a 18 (by decide)⟩

theorem cleanupCost_le (a : Data) (W : ℕ) (hw : ∀i,(a.stacks i).length ≤ W) :
    cleanupCost a ≤ 2*W+6+cleanupPorts.length*(2*W+3) := by
  have hs : (cleanupPorts.map (fun i => (a.stacks i).length)).sum ≤ cleanupPorts.length*W := by
    induction cleanupPorts with
    | nil => simp
    | cons i is ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        have := hw i
        nlinarith
  have := hw 699
  unfold cleanupCost
  nlinarith

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
