import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExportsOps

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem source_ne_destination (f g : Field) (hf : f.Good) (hg : g.Good) : f.src≠g.dst := by
  intro h
  have := congrArg Fin.val h
  dsimp [Field.Good] at hf hg
  omega

theorem destination_ne_scratch (f : Field) (hf : f.Good) :
    f.dst≠659 ∧ f.dst≠660 ∧ f.dst≠661 ∧ f.dst≠679 := by
  dsimp [Field.Good] at hf
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  · intro h; have := congrArg Fin.val h; norm_num at this; omega

theorem ready_of_empty (fs : List Field) (a : Data)
    (hg : ∀ f∈fs, f.Good) (hn : (fs.map Field.dst).Nodup)
    (he : ∀ f∈fs, a.stacks f.dst=[]) (ht : Scratch a) : Ready fs a := by
  induction fs generalizing a with
  | nil => trivial
  | cons f fs ih =>
    have hf := hg f List.mem_cons_self
    have hfd := he f List.mem_cons_self
    have hn' := List.nodup_cons.mp (show (f.dst :: fs.map Field.dst).Nodup from hn)
    have hdiff : ∀ g∈fs, g.dst≠f.dst := by
      intro g hgm h
      apply hn'.1
      exact List.mem_map.mpr ⟨g,hgm,h⟩
    have hst := field_stacks f hf a hfd
    refine ⟨hf,hfd,ht,ih _ (fun g hgm => hg g (List.mem_cons_of_mem _ hgm)) hn'.2 ?_ ?_⟩
    · intro g hgm
      rw [hst,Function.update_of_ne (hdiff g hgm)]
      exact he g (List.mem_cons_of_mem _ hgm)
    · obtain ⟨h1,h2,h3,h4⟩ := destination_ne_scratch f hf
      simpa only [Scratch,hst,Function.update_of_ne h1.symm,
        Function.update_of_ne h2.symm,Function.update_of_ne h3.symm,
        Function.update_of_ne h4.symm] using ht

theorem payload_frame (f g : Field) (hf : f.Good) (hg : g.Good) (a : Data)
    (hd : a.stacks f.dst=[]) : payload g (fieldState f a)=payload g a := by
  simp only [payload,field_stacks f hf a hd,
    Function.update_of_ne (source_ne_destination g f hg hf)]

theorem cost_frame (f g : Field) (hf : f.Good) (hg : g.Good) (a : Data)
    (hd : a.stacks f.dst=[]) : fieldCost g (fieldState f a)=fieldCost g a := by
  simp only [fieldCost,field_stacks f hf a hd,
    Function.update_of_ne (source_ne_destination g f hg hf)]

theorem ready_good (fs : List Field) (a : Data) (h : Ready fs a) : ∀ f∈fs, f.Good := by
  induction fs generalizing a with
  | nil => simp
  | cons f fs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact h.1
    · exact ih _ h.2.2.2 g hg

theorem budget_eq_sum (fs : List Field) (a : Data) (h : Ready fs a) :
    budget fs a=(fs.map (fun f => fieldCost f a)).sum := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih =>
    simp only [budget,List.map_cons,List.sum_cons]
    rw [ih _ h.2.2.2]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro g hg
    exact cost_frame f g h.1 (ready_good fs _ h.2.2.2 g hg) a h.2.1

theorem final_output (fs : List Field) (a : Data) (h : Ready fs a)
    (hn : (fs.map Field.dst).Nodup) (g : Field) (hg : g∈fs) :
    (finalState fs a).stacks g.dst=payload g a := by
  induction fs generalizing a with
  | nil => simp at hg
  | cons f fs ih =>
    have hn' := List.nodup_cons.mp (show (f.dst :: fs.map Field.dst).Nodup from hn)
    rcases List.mem_cons.mp hg with rfl|hg
    · rw [finalState,final_stack_frame fs _ h.2.2.2 g.dst]
      · rw [field_stacks g h.1 a h.2.1,Function.update_self]
      · intro k hk heq
        exact hn'.1 (List.mem_map.mpr ⟨k,hk,heq⟩)
    · exact (ih _ h.2.2.2 hn'.2 hg).trans
        (payload_frame f g h.1 (ready_good fs _ h.2.2.2 g hg) a h.2.1)

/-- The first five fields require numeric binary-to-unary conversion. Fields
5--7 are already true-unary results of the paid cache preparation. -/
def localSource : Fin 16 → Fin 64 := ![0,5,18,21,47,51,52,53,21,18,25,7,1,3,5,29]
def destination : Fin 16 → Fin 768 :=
  ![128,129,130,131,132,138,139,140,720,721,722,723,724,725,726,727]
def field (i : Fin 16) : Field :=
  ⟨⟨340+(localSource i).val,by have := (localSource i).isLt; omega⟩,
    destination i,decide (i.val < 5)⟩
def fields : List Field := (List.finRange 16).map field

theorem fields_good : ∀ f∈fields, f.Good := by
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  fin_cases i <;> simp [Field.Good,field,localSource,destination]
theorem fields_nodup : (fields.map Field.dst).Nodup := by decide
theorem field_mem (i : Fin 16) : field i∈fields := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

def OutputEmpty (a : Data) : Prop := ∀ i, a.stacks (destination i)=[]

theorem fields_ready (a : Data) (ho : OutputEmpty a) (ht : Scratch a) : Ready fields a := by
  apply ready_of_empty fields a fields_good fields_nodup _ ht
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact ho i

def exportCommand : Code := command fields
def exportState (a : Data) : Data := finalState fields a
def exportBudget (a : Data) : ℕ := (fields.map (fun f => fieldCost f a)).sum

theorem export_eval (a : Data) (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ n  ≤  exportBudget a, Eval exportCommand n a (exportState a) := by
  have hr := fields_ready a ho ht
  simpa only [exportCommand,exportState,exportBudget,budget_eq_sum fields a hr] using
    command_eval fields a hr

theorem export_output (a : Data) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 16) :
    (exportState a).stacks (destination i)=payload (field i) a :=
  final_output fields a (fields_ready a ho ht) fields_nodup (field i) (field_mem i)

theorem export_stack_frame (a : Data) (ho : OutputEmpty a) (ht : Scratch a)
    (j : Fin 768) (hj : ∀ i, destination i≠j) : (exportState a).stacks j=a.stacks j := by
  apply final_stack_frame fields a (fields_ready a ho ht) j
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact hj i

theorem export_register_frame (a : Data) (j : Fin 40) (hj : 3 ≤ j.val) :
    (exportState a).regs j=a.regs j := final_register_frame fields a j hj

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
