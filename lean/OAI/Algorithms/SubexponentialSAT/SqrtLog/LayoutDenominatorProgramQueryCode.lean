import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramModel
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev LocalData := State 16 768
abbrev Data := State 40 768

def port (i : Fin 256) : Fin 768 := ⟨340+i.val, by omega⟩
theorem port_injective : Function.Injective port := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [port] using this

def bank : List (Fin 768) := (List.finRange 256).map port

theorem mem_bank (i : Fin 768) : i∈bank ↔ 340 ≤ i.val ∧ i.val < 596 := by
  simp only [bank,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; simp only [port]; omega
  · intro h
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

def pairs : List (Fin 768 × Fin 768) :=
  [(194,534),(201,541),(202,542),(203,543),(204,544),
   (280,589),(207,590),(211,591),(740,579),(253,593)]

theorem pairs_valid : ∀p∈pairs,p.1≠p.2 ∧ p.1≠460 ∧ (460:Fin 768)≠p.2 := by simp [pairs]
theorem pairs_separated : ∀p∈pairs,∀q∈pairs,p.1≠q.2 := by simp [pairs]
theorem pairs_distinct : (pairs.map Prod.snd).Nodup := by decide
theorem pairs_destination : ∀p∈pairs,p.2∈bank := by
  intro p hp
  rw [mem_bank]
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

def staged (a : LocalData) : LocalData := copyManyState pairs a
def view (a : LocalData) : SubexpConvolutionControl.Data :=
  ⟨a.regs,fun i => a.stacks (port i)⟩

abbrev nativeCall : Cmd 16 768 := .call
  (ProgramLinking.liftProgram LayoutDenominatorProgram.program id port)

abbrev localCommand : Cmd 16 768 := .seq (copyMany 460 pairs)
  (.seq nativeCall (.seq (copyCmd 592 728 460) (clearMany bank)))

def registers (i : Fin 16) : Fin 40 := ⟨i.val,by omega⟩
theorem registers_injective : Function.Injective registers := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 40 => k.val) h

def localProgram := compiled localCommand 740 728
abbrev command : Cmd 40 768 := .call (ProgramLinking.liftProgram localProgram registers id)

def budget (R t d W : ℕ) : ℕ := LayoutDenominatorProgram.budget R t d + 600*(W+2)

def localInput (a : LocalData) : SubexpConvolutionControl.Store := fun i =>
  if i=194 then a.stacks 194 else
  if i=201 then a.stacks 201 else
  if i=202 then a.stacks 202 else
  if i=203 then a.stacks 203 else
  if i=204 then a.stacks 204 else
  if i=249 then a.stacks 280 else
  if i=250 then a.stacks 207 else
  if i=251 then a.stacks 211 else
  if i=239 then a.stacks 740 else
  if i=253 then a.stacks 253 else []

theorem staged_view (a : LocalData) (hc : ∀i∈bank,a.stacks i=[]) :
    (view (staged a)).stacks = localInput a := by
  funext i
  have hz := hc (port i) (by rw [mem_bank]; simp only [port]; omega)
  have val (p : Fin 768 × Fin 768) (hp : p∈pairs) :=
    copyMany_value pairs a pairs_distinct (fun p hp => hc p.2 (pairs_destination p hp))
      pairs_separated p hp
  by_cases h194 : i=194
  · subst i
    change (staged a).stacks 534=a.stacks 194
    exact val (194,534) (by simp [pairs])
  by_cases h201 : i=201
  · subst i
    change (staged a).stacks 541=a.stacks 201
    exact val (201,541) (by simp [pairs])
  by_cases h202 : i=202
  · subst i
    change (staged a).stacks 542=a.stacks 202
    exact val (202,542) (by simp [pairs])
  by_cases h203 : i=203
  · subst i
    change (staged a).stacks 543=a.stacks 203
    exact val (203,543) (by simp [pairs])
  by_cases h204 : i=204
  · subst i
    change (staged a).stacks 544=a.stacks 204
    exact val (204,544) (by simp [pairs])
  by_cases h249 : i=249
  · subst i
    change (staged a).stacks 589=a.stacks 280
    exact val (280,589) (by simp [pairs])
  by_cases h250 : i=250
  · subst i
    change (staged a).stacks 590=a.stacks 207
    exact val (207,590) (by simp [pairs])
  by_cases h251 : i=251
  · subst i
    change (staged a).stacks 591=a.stacks 211
    exact val (211,591) (by simp [pairs])
  by_cases h239 : i=239
  · subst i
    change (staged a).stacks 579=a.stacks 740
    exact val (740,579) (by simp [pairs])
  by_cases h253 : i=253
  · subst i
    change (staged a).stacks 593=a.stacks 253
    exact val (253,593) (by simp [pairs])
  have hp : ∀p∈pairs,port i≠p.2 := by
    intro p hp
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      intro he <;> have hv := congrArg Fin.val he <;>
      simp only [port] at hv <;>
      simp only [Fin.ext_iff] at h194 h201 h202 h203 h204 h249 h250 h251 h239 h253 <;> omega
  change (copyManyState pairs a).stacks (port i)=_
  rw [copyMany_frame pairs a (port i) hp,hz]
  simp [localInput,h194,h201,h202,h203,h204,h249,h250,h251,h239,h253]

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
