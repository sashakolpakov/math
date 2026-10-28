import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramWide

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def exportPairs : List (Fin 768 × Fin 768) :=
  [(ports 62,133),(ports 63,135),(ports 61,136)]
def privatePorts : List (Fin 768) := (List.finRange 64).map ports
abbrev exportLocal : Cmd 16 768 := .seq (copyMany 684 exportPairs) (clearMany privatePorts)
def exported (a : Local) : Local := clearManyState privatePorts (copyManyState exportPairs a)
def exportCost (a : Local) := copyManyCost exportPairs a+
  clearManyCost privatePorts (copyManyState exportPairs a)

theorem exportLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval exportLocal (exportCost a) a (exported a) :=
  (copyMany_eval 684 exportPairs a (by
    intro p hp
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> decide) ht).seq
    (clearMany_eval privatePorts (copyManyState exportPairs a))

theorem mem_privatePorts (i : Fin 768) :
    i∈privatePorts ↔ 417 ≤ i.val ∧ i.val < 481 := by
  simp only [privatePorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,rfl⟩; have := j.isLt; change 417 ≤ 417+j.val ∧ 417+j.val < 481; omega
  · rintro ⟨hl,hu⟩
    refine ⟨⟨i.val-417,by omega⟩,?_⟩
    apply Fin.ext
    change 417+(i.val-417)=i.val
    omega

theorem exported_bank (a : Local) (i : Fin 64) :
    (exported a).stacks (ports i)=[] := by
  rw [exported,clearMany_stacks,ite_eq_left]
  exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

theorem exported_frame (a : Local) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (h133 : i≠133) (h135 : i≠135) (h136 : i≠136) :
    (exported a).stacks i=a.stacks i := by
  rw [exported,clearMany_stacks,ite_eq_right (by rw [mem_privatePorts]; omega)]
  apply copyMany_frame
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
  rintro p (rfl|rfl|rfl) <;> assumption

theorem exported_value (a : Local)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[])
    (p : Fin 768 × Fin 768) (hp : p∈exportPairs) :
    (exported a).stacks p.2=a.stacks p.1 := by
  have hd : p.2∉privatePorts := by
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> simp [mem_privatePorts]
  rw [exported,clearMany_stacks,ite_eq_right hd]
  apply copyMany_value exportPairs a (by decide) ?_ ?_ p hp
  · simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
    rintro q (rfl|rfl|rfl) <;> assumption
  · intro q hq z hz
    simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hq hz
    rcases hq with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl <;> decide

theorem parked_frame (a : Local) (i : Fin 768)
    (hl : i.val < 128 ∨ 142 ≤ i.val) (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (LeafProgram.LayoutMasters.parked a).stacks i=a.stacks i := by
  rw [LeafProgram.LayoutMasters.parked,clearMany_stacks,ite_eq_right]
  · apply copyMany_frame
    intro p hp he
    simp only [LeafProgram.LayoutMasters.parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
    obtain ⟨j,rfl⟩ := hp
    have hv := congrArg Fin.val he
    change i.val=730+j.val at hv
    have := j.isLt
    omega
  · simp only [LeafProgram.LayoutMasters.lowPorts,List.mem_map,List.mem_finRange,true_and]
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 128+j.val=i.val at hv
    have := j.isLt
    omega

abbrev finishLocal : Cmd 16 768 := .seq exportLocal LeafProgram.LayoutMasters.parkLocal
def finished (a : Local) : Local := LeafProgram.LayoutMasters.parked (exported a)
def finishCost (a : Local) := exportCost a+LeafProgram.LayoutMasters.parkCost (exported a)

theorem finishLocal_eval (a : Local) (ht : a.stacks 684=[]) :
    Eval finishLocal (finishCost a) a (finished a) := by
  apply (exportLocal_eval a ht).seq
  apply LeafProgram.LayoutMasters.park_local_eval
  rw [exported_frame a 684 (by norm_num) (by decide) (by decide) (by decide),ht]

def finish : Code := call finishLocal
theorem finish_eval (a : Data) (ht : a.stacks 684=[]) :
    ∃ b, Eval finish (finishCost (project a)+1) a b ∧
      b.stacks=(finished (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) :=
  call_eval finishLocal a _ _ (finishLocal_eval (project a) ht)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
