import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationUnary
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Paid metadata exports. These commands touch only their destination and
three working registers; binary sources and all scratch words are restored. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

structure Field where
  src : Fin 768
  dst : Fin 768
  unary : Bool
  deriving DecidableEq

def Field.Good (f : Field) : Prop :=
  340  ≤  f.src.val ∧ f.src.val < 417 ∧
    ((128  ≤  f.dst.val ∧ f.dst.val  ≤  140) ∨ (720  ≤  f.dst.val ∧ f.dst.val  ≤  727))

def regs : Fin 3 → Fin 40 := Fin.castAdd 37

def ports (f : Field) (i : Fin 14) : Fin 768 :=
  if i.val=0 then f.src else if i.val=1 then f.dst else ⟨648+i.val,by omega⟩

theorem ports_injective (f : Field) (hf : f.Good) : Function.Injective (ports f) := by
  intro i j h
  dsimp [Field.Good] at hf
  fin_cases i <;> fin_cases j <;> simp_all [ports,Fin.ext_iff]
  all_goals omega

def payload (f : Field) (a : Data) : List Bool :=
  if f.unary then List.replicate (BinaryArithmetic.toNat (a.stacks f.src)) true else a.stacks f.src

def fieldCommand (f : Field) : Code :=
  if f.unary then liftCommand (Serialization.unaryCopy 0 1) 0 1 regs (ports f)
  else .call (StackRoutines.copyProgram f.src f.dst 679 0 1)

def fieldState (f : Field) (a : Data) : Data :=
  if f.unary then embedState regs (ports f) a
    (SubexpClauseMastersProgram.write (projectState regs (ports f) a) 1 (payload f a))
  else SubexpScanPrimitives.afterCopy a f.src f.dst 0 1

def fieldCost (f : Field) (a : Data) : ℕ :=
  if f.unary then Serialization.unaryCopyBound (a.stacks f.src)+1
  else 7*(a.stacks f.src).length+5

def Scratch (a : Data) : Prop :=
  a.stacks 659=[] ∧ a.stacks 660=[] ∧ a.stacks 661=[] ∧ a.stacks 679=[]

theorem field_eval (f : Field) (hf : f.Good) (a : Data)
    (hd : a.stacks f.dst=[]) (ht : Scratch a) :
    ∃ n  ≤  fieldCost f a, Eval (fieldCommand f) n a (fieldState f a) := by
  by_cases hu : f.unary=true
  · let d := projectState regs (ports f) a
    obtain ⟨n,hn,he⟩ := Serialization.unaryCopy_eval 0 1 d
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [d,projectState,ports] using hd)
      (by simpa [d,projectState,ports] using ht.1)
      (by simpa [d,projectState,ports] using ht.2.1)
      (by simpa [d,projectState,ports] using ht.2.2.1)
    refine ⟨n+1,?_,?_⟩
    · simpa [fieldCost,hu,d,projectState,ports] using Nat.add_le_add_right hn 1
    · simpa [fieldCommand,fieldState,payload,hu,d,projectState,ports] using
        eval_liftCommand_from_state (Serialization.unaryCopy 0 1) 0 1 regs (ports f) a
          (Fin.castAdd_injective _ _) (ports_injective f hf) he
  · have hf' := hf
    dsimp [Field.Good] at hf'
    have hsd : f.src≠f.dst := by intro h; have := congrArg Fin.val h; omega
    have hst : f.src≠679 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htd : (679 : Fin 768)≠f.dst := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    refine ⟨7*(a.stacks f.src).length+5,by simp [fieldCost,hu],?_⟩
    simpa [fieldCommand,fieldState,hu] using
      SubexpScanPrimitives.copy_eval a f.src f.dst 679 0 1 hsd hst htd (by decide) ht.2.2.2

theorem field_stacks (f : Field) (hf : f.Good) (a : Data) (hd : a.stacks f.dst=[]) :
    (fieldState f a).stacks=Function.update a.stacks f.dst (payload f a) := by
  by_cases hu : f.unary=true
  · let d := projectState regs (ports f) a
    have hb : (embedState regs (ports f) a
        (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data)).stacks=a.stacks := by
      change (embedState regs (ports f) a d).stacks=a.stacks
      exact congrArg (fun z => z.stacks)
        (embedState_project regs (ports f) a (Fin.castAdd_injective _ _) (ports_injective f hf))
    simp only [fieldState,hu,ite_true]
    dsimp only [SubexpClauseMastersProgram.write]
    rw [show (⟨SubexpClauseMastersProgram.zeroRegs,
      Function.update (projectState regs (ports f) a).stacks 1 (payload f a)⟩ : Serialization.Data)=
      { (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data) with
        «stacks» := Function.update d.stacks 1 (payload f a) } by rfl]
    rw [embedState_update_stack regs (ports f) a _ (ports_injective f hf) 1 (payload f a)]
    simpa [ports] using congrArg (fun w => Function.update w f.dst (payload f a)) hb
  · simp [fieldState,hu,payload,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hd]

theorem field_register_frame (f : Field) (a : Data) (i : Fin 40) (hi : 3 ≤ i.val) :
    (fieldState f a).regs i=a.regs i := by
  by_cases hu : f.unary=true
  · simp only [fieldState,hu,ite_true]
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have := congrArg Fin.val hj
    dsimp [regs] at this
    omega
  · have h0 : i≠0 := by intro h; subst i; norm_num at hi
    have h1 : i≠1 := by intro h; subst i; norm_num at hi
    simp [fieldState,hu,SubexpScanPrimitives.afterCopy,readRegs,h0,h1]

def command : List Field → Code
  | [] => .base .skip
  | f::fs => .seq (fieldCommand f) (command fs)
def finalState : List Field → Data → Data
  | [],a => a
  | f::fs,a => finalState fs (fieldState f a)
def budget : List Field → Data → ℕ
  | [],_ => 0
  | f::fs,a => fieldCost f a+budget fs (fieldState f a)
def Ready : List Field → Data → Prop
  | [],_ => True
  | f::fs,a => f.Good ∧ a.stacks f.dst=[] ∧ Scratch a ∧ Ready fs (fieldState f a)

theorem command_eval (fs : List Field) (a : Data) (h : Ready fs a) :
    ∃ n  ≤  budget fs a, Eval (command fs) n a (finalState fs a) := by
  induction fs generalizing a with
  | nil => exact ⟨0,le_rfl,.base (.skip a)⟩
  | cons f fs ih =>
    obtain ⟨n,hn,he⟩ := field_eval f h.1 a h.2.1 h.2.2.1
    obtain ⟨k,hk,hke⟩ := ih _ h.2.2.2
    exact ⟨n+k,Nat.add_le_add hn hk,he.seq hke⟩

theorem final_register_frame (fs : List Field) (a : Data) (i : Fin 40) (hi : 3 ≤ i.val) :
    (finalState fs a).regs i=a.regs i := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih => exact (ih _).trans (field_register_frame f a i hi)

theorem final_stack_frame (fs : List Field) (a : Data) (h : Ready fs a)
    (i : Fin 768) (hi : ∀ f∈fs, f.dst≠i) : (finalState fs a).stacks i=a.stacks i := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih =>
    rw [finalState,ih _ h.2.2.2 (fun g hg => hi g (List.mem_cons_of_mem _ hg)),
      field_stacks f h.1 a h.2.1]
    exact Function.update_of_ne (Ne.symm (hi f List.mem_cons_self)) _ _

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
