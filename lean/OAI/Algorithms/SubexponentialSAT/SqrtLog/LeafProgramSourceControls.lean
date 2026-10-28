import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceStaging

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def pairs : List (Fin 768 × Fin 768) :=
  [(130,361),(131,362),(132,366),
   (710,382),(711,383),(140,384),(712,385),(138,387),(139,388),
   (135,646),(713,648),(714,649),(715,650),(717,651),(716,652),
   (280,653),(207,654),(136,677),
   (280,589),(207,590),(211,591),(728,592)]

abbrev setDelta : Cmd 16 768 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 365 0)))
def deltaState (a : Data) : Data :=
  (StructuredProgram.Atom.push (365 : Fin 768) (0 : Fin 16)).eval
    ((StructuredProgram.Atom.set (0 : Fin 16) true).eval a)

abbrev prepare : Cmd 16 768 := .seq (copyMany 684 pairs) setDelta
def prepared (a : Data) : Data := deltaState (copyManyState pairs a)
def prepareCost (a : Data) : ℕ := copyManyCost pairs a + 2

theorem pairs_valid : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

theorem setDelta_eval (a : Data) : Eval setDelta 2 a (deltaState a) :=
  (Eval.base (StructuredProgram.Eval.atom (.set 0 true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push 365 0)
      ((StructuredProgram.Atom.set (0 : Fin 16) true).eval a)))

theorem prepare_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval prepare (prepareCost a) a (prepared a) :=
  (copyMany_eval 684 pairs a pairs_valid htmp).seq (setDelta_eval _)

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

def extraPorts : List (Fin 768) :=
  [589,590,591,592] ++ (List.finRange 84).map (fun i => (⟨596+i.val, by omega⟩ : Fin 768))
abbrev cleanup : Cmd 16 768 := clearMany extraPorts
def cleaned (a : Data) : Data := clearManyState extraPorts a

theorem cleanup_eval (a : Data) :
    Eval cleanup (clearManyCost extraPorts a) a (cleaned a) := clearMany_eval extraPorts a

theorem mem_extraPorts (i : Fin 768) : i ∈ extraPorts ↔
    (589 ≤ i.val ∧ i.val < 593) ∨ (596 ≤ i.val ∧ i.val < 680) := by
  have hr : i ∈ (List.finRange 84).map
      (fun j => (⟨596+j.val,by omega⟩ : Fin 768)) ↔ 596 ≤ i.val ∧ i.val < 680 := by
    simp only [List.mem_map,List.mem_finRange,true_and]
    constructor
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change 596+j.val=i.val at hv
      omega
    · intro hi
      refine ⟨⟨i.val-596,by omega⟩,?_⟩
      apply Fin.ext
      change 596+(i.val-596)=i.val
      omega
  have hc : i ∈ ([589,590,591,592] : List (Fin 768)) ↔ 589 ≤ i.val ∧ i.val < 593 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · intro h
      rcases h with rfl|rfl|rfl|rfl <;> decide
    · intro h
      have hv : i.val=589 ∨ i.val=590 ∨ i.val=591 ∨ i.val=592 := by omega
      rcases hv with h|h|h|h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; left; exact Fin.ext h
      · right; right; right; exact Fin.ext h
  simp only [extraPorts,List.mem_append,hc,hr]

theorem cleaned_extra (a : Data) (i : Fin 768) (hi : 596 ≤ i.val ∧ i.val < 680) :
    (cleaned a).stacks i = [] := by
  rw [cleaned,clearMany_stacks,ite_eq_left ((mem_extraPorts i).mpr (Or.inr hi))]

theorem cleaned_frame (a : Data) (i : Fin 768)
    (hi : ¬((589 ≤ i.val ∧ i.val < 593) ∨ (596 ≤ i.val ∧ i.val < 680))) :
    (cleaned a).stacks i = a.stacks i := by
  rw [cleaned,clearMany_stacks,ite_eq_right (fun h => hi ((mem_extraPorts i).mp h))]

/-- The source length is R+1, independently of the target Z-jet order. -/
abbrev cutoff : Cmd 16 768 := .seq (copyCmd 138 550 684)
  (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 550 0))))
def cutoffState (a : Data) : Data :=
  ⟨Function.update (readRegs a.regs 0 1 none) 0 true,
    Function.update a.stacks 550 (true :: (a.stacks 138 ++ a.stacks 550))⟩

theorem cutoff_eval (a : Data) (htmp : a.stacks 684 = []) :
    Eval cutoff (7*(a.stacks 138).length+7) a (cutoffState a) := by
  have hc := SubexpSetupStorage.copy_eval 138 550 684 a
    (by decide) (by decide) (by decide) htmp
  have hs := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 16) true)
    (copyState 138 550 a))
  have hp := Eval.base (StructuredProgram.Eval.atom (.push (550 : Fin 768) (0 : Fin 16))
    ((StructuredProgram.Atom.set (0 : Fin 16) true).eval (copyState 138 550 a)))
  have hstate : (StructuredProgram.Atom.push (550 : Fin 768) (0 : Fin 16)).eval
      ((StructuredProgram.Atom.set (0 : Fin 16) true).eval (copyState 138 550 a)) =
      cutoffState a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 550
      · subst i
        simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          copyState,StackRoutines.copyStacks]
      · simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          copyState,StackRoutines.copyStacks,hi]
  rw [hstate] at hp
  convert hc.seq (hs.seq hp) using 1

theorem cutoff_value (a : Data) (R : ℕ)
    (hR : a.stacks 138 = List.replicate R true) (hempty : a.stacks 550 = []) :
    (cutoffState a).stacks 550 = List.replicate (R+1) true := by
  simp [cutoffState,hR,hempty,List.replicate_succ]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
