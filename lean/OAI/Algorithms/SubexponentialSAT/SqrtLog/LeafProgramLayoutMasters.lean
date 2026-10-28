import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev LocalData := State 16 768
abbrev Data := State 40 768
def low (i : Fin 14) : Fin 768 := ⟨128+i.val,by omega⟩
def high (i : Fin 14) : Fin 768 := ⟨730+i.val,by omega⟩
def lowPorts : List (Fin 768) := (List.finRange 14).map low
def parkPairs : List (Fin 768 × Fin 768) := (List.finRange 14).map fun i => (low i,high i)
def loadPairs : List (Fin 768 × Fin 768) := (List.finRange 14).map fun i => (high i,low i)

abbrev parkLocal : Cmd 16 768 := .seq (copyMany 684 parkPairs) (clearMany lowPorts)
abbrev loadLocal : Cmd 16 768 := copyMany 684 loadPairs
def parked (a : LocalData) := clearManyState lowPorts (copyManyState parkPairs a)
def loaded (a : LocalData) := copyManyState loadPairs a
def parkCost (a : LocalData) := copyManyCost parkPairs a+
  clearManyCost lowPorts (copyManyState parkPairs a)
def loadCost (a : LocalData) := copyManyCost loadPairs a

theorem park_valid : ∀ p ∈ parkPairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  constructor
  · intro h; have hv := congrArg Fin.val h; change 128+i.val=730+i.val at hv; omega
  constructor
  · intro h; have hv := congrArg Fin.val h; change 128+i.val=684 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change 684=730+i.val at hv; omega
theorem load_valid : ∀ p ∈ loadPairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  constructor
  · intro h; have hv := congrArg Fin.val h; change 730+i.val=128+i.val at hv; omega
  constructor
  · intro h; have hv := congrArg Fin.val h; change 730+i.val=684 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change 684=128+i.val at hv; omega

theorem park_local_eval (a : LocalData) (ht : a.stacks 684 = []) :
    Eval parkLocal (parkCost a) a (parked a) :=
  (copyMany_eval 684 parkPairs a park_valid ht).seq
    (clearMany_eval lowPorts (copyManyState parkPairs a))
theorem load_local_eval (a : LocalData) (ht : a.stacks 684 = []) :
    Eval loadLocal (loadCost a) a (loaded a) := copyMany_eval 684 loadPairs a load_valid ht

theorem low_injective : Function.Injective low := by
  intro i j h; apply Fin.ext
  have hv := congrArg Fin.val h
  change 128+i.val=128+j.val at hv
  omega
theorem high_injective : Function.Injective high := by
  intro i j h; apply Fin.ext
  have hv := congrArg Fin.val h
  change 730+i.val=730+j.val at hv
  omega

theorem park_nodup : (parkPairs.map Prod.snd).Nodup := by
  simpa only [parkPairs,List.map_map,Function.comp_def] using
    (List.nodup_finRange 14).map high_injective
theorem load_nodup : (loadPairs.map Prod.snd).Nodup := by
  simpa only [loadPairs,List.map_map,Function.comp_def] using
    (List.nodup_finRange 14).map low_injective
theorem park_sep : ∀ p ∈ parkPairs, ∀ q ∈ parkPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp hq
  obtain ⟨i,rfl⟩ := hp
  obtain ⟨j,rfl⟩ := hq
  intro h
  have hv := congrArg Fin.val h
  change 128+i.val=730+j.val at hv
  omega
theorem load_sep : ∀ p ∈ loadPairs, ∀ q ∈ loadPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp hq
  obtain ⟨i,rfl⟩ := hp
  obtain ⟨j,rfl⟩ := hq
  intro h
  have hv := congrArg Fin.val h
  change 730+i.val=128+j.val at hv
  omega

theorem parked_high (a : LocalData) (hz : ∀ i, a.stacks (high i) = []) (i : Fin 14) :
    (parked a).stacks (high i) = a.stacks (low i) := by
  have hout : high i ∉ lowPorts := by
    simp only [lowPorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j h
    have hv := congrArg Fin.val h
    change 128+j.val=730+i.val at hv
    omega
  rw [parked,clearMany_stacks,ite_eq_right hout]
  exact copyMany_value parkPairs a park_nodup
    (by intro p hp; simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨j,rfl⟩ := hp; exact hz j)
    park_sep (low i,high i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem parked_low (a : LocalData) (i : Fin 14) : (parked a).stacks (low i) = [] := by
  rw [parked,clearMany_stacks,ite_eq_left]
  exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

theorem loaded_low (a : LocalData) (hz : ∀ i, a.stacks (low i) = []) (i : Fin 14) :
    (loaded a).stacks (low i) = a.stacks (high i) := by
  exact copyMany_value loadPairs a load_nodup
    (by intro p hp; simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨j,rfl⟩ := hp; exact hz j)
    load_sep (high i,low i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem loaded_frame (a : LocalData) (j : Fin 768) (hj : j ∉ lowPorts) :
    (loaded a).stacks j = a.stacks j := by
  apply copyMany_frame
  intro p hp he
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  apply hj
  exact List.mem_map.mpr ⟨i,List.mem_finRange i,he.symm⟩

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def project (a : Data) : LocalData := ⟨a.regs ∘ registers,a.stacks⟩
abbrev park : Cmd 40 768 := .call (ProgramLinking.liftProgram (compiled parkLocal 128 730) registers id)
abbrev load : Cmd 40 768 := .call (ProgramLinking.liftProgram (compiled loadLocal 730 128) registers id)

private theorem installed_stacks (a : Data) (b : LocalData) :
    (embedState registers id a b).stacks = b.stacks := by
  funext i
  exact embedState_stack registers id a b Function.injective_id i

private theorem installed_registers (a : Data) (b : LocalData) (i : Fin 40) (hi : 16 ≤ i.val) :
    (embedState registers id a b).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem park_eval (a : Data) (ht : a.stacks 684 = []) :
    ∃ b, Eval park (parkCost (project a)+1) a b ∧
      b.stacks = (parked (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i = a.regs i) := by
  have h := park_local_eval (project a) ht
  have he := eval_call_from_state (compiled parkLocal 128 730) registers id a
    (Fin.castAdd_injective _ _) Function.injective_id (compiled_halt_trace h 128 730)
  exact ⟨_,he,installed_stacks a _,installed_registers a _⟩

theorem load_eval (a : Data) (ht : a.stacks 684 = []) :
    ∃ b, Eval load (loadCost (project a)+1) a b ∧
      b.stacks = (loaded (project a)).stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i = a.regs i) := by
  have h := load_local_eval (project a) ht
  have he := eval_call_from_state (compiled loadLocal 730 128) registers id a
    (Fin.castAdd_injective _ _) Function.injective_id (compiled_halt_trace h 730 128)
  exact ⟨_,he,installed_stacks a _,installed_registers a _⟩

theorem loadCost_le (a : LocalData) (B : ℕ) (h : ∀ i,(a.stacks (high i)).length ≤ B) :
    loadCost a ≤ 14*(7*B+5) := by
  apply copyManyCost_le loadPairs a B load_sep
  intro p hp
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  exact h i

theorem parkCost_le (a : LocalData) (B : ℕ) (h : WordBound B a)
    (hz : ∀ i,a.stacks (high i)=[]) : parkCost a ≤ 14*(9*B+8) := by
  have hc := copyManyCost_le parkPairs a B park_sep (fun p hp => h p.1)
  have hw := copyMany_wordBound parkPairs a B park_nodup
    (by intro p hp; simp only [parkPairs,List.mem_map,List.mem_finRange,true_and] at hp
        obtain ⟨i,rfl⟩ := hp; exact hz i) park_sep h
  have hd := clearManyCost_le lowPorts (copyManyState parkPairs a) B hw
  change copyManyCost parkPairs a ≤ 14*(7*B+5) at hc
  change clearManyCost lowPorts (copyManyState parkPairs a) ≤ 14*(2*B+3) at hd
  unfold parkCost
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
