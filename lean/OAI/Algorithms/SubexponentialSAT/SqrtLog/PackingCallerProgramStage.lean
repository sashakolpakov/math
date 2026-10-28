import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramWide

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def stagePairs : List (Fin 768 × Fin 768) :=
  [(718,ports 32),(128,ports 33),(719,ports 36),
   (720,ports 55),(709,ports 56),(722,ports 57),(723,ports 58),(721,ports 59)]
abbrev stageLocal : Cmd 16 768 := copyMany 684 stagePairs
def staged (a : Local) : Local := copyManyState stagePairs a

def parameterStore (a : Local) : Fin 64 → List Bool := fun i=>
  if i=55 then a.stacks 720 else if i=56 then a.stacks 709
  else if i=57 then a.stacks 722 else if i=58 then a.stacks 723
  else if i=59 then a.stacks 721 else []

def BankEmpty (a : Local) : Prop := ∀ i,a.stacks (ports i)=[]

theorem stageLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval stageLocal (copyManyCost stagePairs a) a (staged a) :=
  copyMany_eval 684 stagePairs a (by
    intro p hp
    simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) ht

theorem staged_bank (a : Local) (hbank : BankEmpty a)
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hscopes : a.stacks 718=Scan.scopeBits scopes)
    (hn : a.stacks 128=Scan.unary n) (hmask : a.stacks 719=mask) :
    projectState id ports (staged a)=
      framed (parameterStore a) (Install.input (staged a).regs scopes n mask) := by
  rw [Entry.install_eq]
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · simp [projectState]
  · have hclear : ∀ p ∈ stagePairs, a.stacks p.2 = [] := by
      intro p hp
      simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hbank _
    have hsep : ∀ p ∈ stagePairs, ∀ q ∈ stagePairs, p.1 ≠ q.2 := by
      intro p hp q hq
      simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp hq
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    have hvalue (p : Fin 768 × Fin 768) (hp : p ∈ stagePairs) :
        (staged a).stacks p.2 = a.stacks p.1 := by
      exact copyMany_value stagePairs a (by decide) hclear hsep p hp
    have hframe (i : Fin 64)
        (hi : i ∉ [(32 : Fin 64),33,36,55,56,57,58,59]) :
        (staged a).stacks (ports i) = [] := by
      rw [show (staged a).stacks (ports i) = a.stacks (ports i) from copyMany_frame _ _ _ (by
        intro p hp
        simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all)]
      exact hbank i
    have h32 := hvalue ((718 : Fin 768),ports 32) (by simp [stagePairs])
    have h33 := hvalue ((128 : Fin 768),ports 33) (by simp [stagePairs])
    have h36 := hvalue ((719 : Fin 768),ports 36) (by simp [stagePairs])
    have h55 := hvalue ((720 : Fin 768),ports 55) (by simp [stagePairs])
    have h56 := hvalue ((709 : Fin 768),ports 56) (by simp [stagePairs])
    have h57 := hvalue ((722 : Fin 768),ports 57) (by simp [stagePairs])
    have h58 := hvalue ((723 : Fin 768),ports 58) (by simp [stagePairs])
    have h59 := hvalue ((721 : Fin 768),ports 59) (by simp [stagePairs])
    funext i
    fin_cases i <;> simp [projectState,framed_stack,parameterStore,Entry.sourceStacks,
      hscopes,hn,hmask,h32,h33,h36,h55,h56,h57,h58,h59,hframe]

theorem staged_frame (a : Local) (j : Fin 768)
    (hj : j.val < 417 ∨ 481 ≤ j.val) : (staged a).stacks j=a.stacks j := by
  apply copyMany_frame
  intro p hp h
  simp only [stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    have hv := congrArg Fin.val h <;> simp only [ports_val] at hv <;> omega

def stage : Code := call stageLocal

theorem stage_eval (a : Data) (ht : a.stacks 684=[]) :
    ∃ b, Eval stage (copyManyCost stagePairs (project a)+1) a b ∧
      b.stacks=(staged (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) :=
  call_eval stageLocal a (staged (project a)) _ (stageLocal_eval (project a) ht)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
