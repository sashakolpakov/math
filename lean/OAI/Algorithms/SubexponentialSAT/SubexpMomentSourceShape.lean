import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyCost

namespace OAI.Algorithms

/-! Encoded lengths and actual assembly counts depend only on weight lengths
and retained factor data. -/

namespace SubexponentialSAT.SubexpMomentSourceShape

open SubexpKernelControl (Word)

theorem encoded_length_congr {α β : Type*} (f : α → Word) (g : β → Word)
    {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun x y => (f x).length = (g y).length) xs ys) :
    (Encoding.encodeList f xs).length = (Encoding.encodeList g ys).length := by
  induction h with
  | nil => rfl
  | cons he ht ih =>
      simp only [Encoding.length_encodeList_cons,he,ih]

theorem map_related {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
    (f : α → γ) (g : β → δ) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hh : ∀ x y, R x y → S (f x) (g y)) :
    List.Forall₂ S (xs.map f) (ys.map g) := by
  induction h with
  | nil => exact .nil
  | cons he ht ih => exact .cons (hh _ _ he) ih

theorem map_related_rev {α β γ δ : Type*} {R : α → β → Prop} {S : δ → γ → Prop}
    (f : α → γ) (g : β → δ) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hh : ∀ x y, R x y → S (g y) (f x)) :
    List.Forall₂ S (ys.map g) (xs.map f) := by
  induction h with
  | nil => exact .nil
  | cons he ht ih => exact .cons (hh _ _ he) ih

theorem sum_map_congr {α β : Type*} {R : α → β → Prop}
    (f : α → ℕ) (g : β → ℕ) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hh : ∀ x y, R x y → f x = g y) :
    (xs.map f).sum = (ys.map g).sum := by
  induction h with
  | nil => rfl
  | cons he ht ih => simp only [List.map_cons,List.sum_cons,hh _ _ he,ih]

def SameTermShape (s t : SubexpBlockAssembly.Term) : Prop :=
  s.weight.length = t.weight.length ∧ s.factors = t.factors

def SameBlockShape (b c : SubexpBlockAssembly.Block) : Prop :=
  b.outside.length = c.outside.length ∧
    List.Forall₂ (List.Forall₂ SameTermShape) b.groups c.groups

theorem term_encoded_length {s t : SubexpBlockAssembly.Term}
    (h : SameTermShape s t) :
    (SubexpBlockAssembly.encodeTerm s).length = (SubexpBlockAssembly.encodeTerm t).length := by
  simp only [SubexpBlockAssembly.encodeTerm,List.length_append,Encoding.length_frame,h.1,h.2]

theorem compiled_term_encoded_length (zero one : Word)
    {s t : SubexpBlockAssembly.Term} (h : SameTermShape s t) :
    (SubexpKernelControl.encodeTerm (SubexpBlockAssembly.compiledTerm zero one s)).length =
      (SubexpKernelControl.encodeTerm (SubexpBlockAssembly.compiledTerm zero one t)).length := by
  simp only [SubexpKernelControl.encodeTerm,SubexpBlockAssembly.compiledTerm,
    Encoding.length_encodeList_cons,Encoding.length_encodeList_nil,id_eq,h.1,h.2]

theorem group_encoded_length {ss ts : List SubexpBlockAssembly.Term}
    (h : List.Forall₂ SameTermShape ss ts) :
    (SubexpBlockAssembly.encodeGroup ss).length = (SubexpBlockAssembly.encodeGroup ts).length :=
  encoded_length_congr _ _ (h.imp (fun _ _ he => term_encoded_length he))

theorem compiled_group_encoded_length (zero one : Word)
    {ss ts : List SubexpBlockAssembly.Term} (h : List.Forall₂ SameTermShape ss ts) :
    (SubexpKernelControl.encodeGroup (ss.map (SubexpBlockAssembly.compiledTerm zero one))).length =
      (SubexpKernelControl.encodeGroup (ts.map (SubexpBlockAssembly.compiledTerm zero one))).length :=
  encoded_length_congr _ _ (map_related _ _ h
    (fun _ _ he => compiled_term_encoded_length zero one he))

theorem groups_encoded_length
    {ss ts : List (List SubexpBlockAssembly.Term)}
    (h : List.Forall₂ (List.Forall₂ SameTermShape) ss ts) :
    (Encoding.encodeList SubexpBlockAssembly.encodeGroup ss).length =
      (Encoding.encodeList SubexpBlockAssembly.encodeGroup ts).length :=
  encoded_length_congr _ _ (h.imp (fun _ _ he => group_encoded_length he))

theorem compiled_groups_encoded_length (zero one : Word)
    {ss ts : List (List SubexpBlockAssembly.Term)}
    (h : List.Forall₂ (List.Forall₂ SameTermShape) ss ts) :
    (Encoding.encodeList SubexpKernelControl.encodeGroup
      (ss.map (List.map (SubexpBlockAssembly.compiledTerm zero one)))).length =
      (Encoding.encodeList SubexpKernelControl.encodeGroup
        (ts.map (List.map (SubexpBlockAssembly.compiledTerm zero one)))).length :=
  encoded_length_congr _ _ (map_related _ _ h
    (fun _ _ he => compiled_group_encoded_length zero one he))

theorem block_encoded_length {b c : SubexpBlockAssembly.Block}
    (h : SameBlockShape b c) :
    (SubexpBlockAssembly.encodeBlock b).length = (SubexpBlockAssembly.encodeBlock c).length := by
  simp only [SubexpBlockAssembly.encodeBlock,List.length_append,Encoding.length_frame,h.1,
    groups_encoded_length h.2]

theorem compiled_block_encoded_length (zero one : Word)
    {b c : SubexpBlockAssembly.Block} (h : SameBlockShape b c) :
    (SubexpKernelControl.encodeBlock (SubexpBlockAssembly.compiledBlock zero one b)).length =
      (SubexpKernelControl.encodeBlock (SubexpBlockAssembly.compiledBlock zero one c)).length := by
  simp only [SubexpKernelControl.encodeBlock,SubexpBlockAssembly.compiledBlock,
    Encoding.length_encodeList_cons,Encoding.length_encodeList_nil,id_eq,h.1,
    compiled_groups_encoded_length zero one h.2]

theorem term_steps_eq (zero one : Word)
    {s t : SubexpBlockAssembly.Term} (h : SameTermShape s t) :
    SubexpBlockAssembly.termSteps zero one s = SubexpBlockAssembly.termSteps zero one t := by
  simp only [SubexpBlockAssembly.termSteps,h.1,h.2,compiled_term_encoded_length zero one h]

theorem group_steps_eq (zero one : Word)
    {ss ts : List SubexpBlockAssembly.Term} (h : List.Forall₂ SameTermShape ss ts) :
    SubexpBlockAssembly.groupSteps zero one ss = SubexpBlockAssembly.groupSteps zero one ts := by
  have hs := sum_map_congr
    (fun t => 9*(SubexpBlockAssembly.encodeTerm t).length+SubexpBlockAssembly.termSteps zero one t+9)
    (fun t => 9*(SubexpBlockAssembly.encodeTerm t).length+SubexpBlockAssembly.termSteps zero one t+9)
    h (fun _ _ he => by rw [term_encoded_length he,term_steps_eq zero one he])
  simp only [SubexpBlockAssembly.groupSteps,hs,compiled_group_encoded_length zero one h]

theorem block_steps_eq (zero one : Word)
    {b c : SubexpBlockAssembly.Block} (h : SameBlockShape b c) :
    SubexpBlockAssembly.blockSteps zero one b = SubexpBlockAssembly.blockSteps zero one c := by
  have hs := sum_map_congr
    (fun ts => 9*(SubexpBlockAssembly.encodeGroup ts).length+SubexpBlockAssembly.groupSteps zero one ts+9)
    (fun ts => 9*(SubexpBlockAssembly.encodeGroup ts).length+SubexpBlockAssembly.groupSteps zero one ts+9)
    h.2 (fun _ _ he => by rw [group_encoded_length he,group_steps_eq zero one he])
  simp only [SubexpBlockAssembly.blockSteps,hs,h.1,
    compiled_groups_encoded_length zero one h.2,compiled_block_encoded_length zero one h]

theorem blocks_encoded_length {bs cs : List SubexpBlockAssembly.Block}
    (h : List.Forall₂ SameBlockShape bs cs) :
    (SubexpBlockAssembly.encodeBlocks bs).length = (SubexpBlockAssembly.encodeBlocks cs).length :=
  encoded_length_congr _ _ (h.imp (fun _ _ he => block_encoded_length he))

theorem assembled_length_eq (zero one : Word) {bs cs : List SubexpBlockAssembly.Block}
    (h : List.Forall₂ SameBlockShape bs cs) :
    (SubexpBlockAssembly.assembled zero one bs).length =
      (SubexpBlockAssembly.assembled zero one cs).length :=
  encoded_length_congr _ _ (map_related _ _ h
    (fun _ _ he => compiled_block_encoded_length zero one he))

theorem assembly_steps_eq (zero one : Word) {bs cs : List SubexpBlockAssembly.Block}
    (h : List.Forall₂ SameBlockShape bs cs) :
    SubexpBlockAssembly.assemblySteps zero one bs = SubexpBlockAssembly.assemblySteps zero one cs := by
  have hs := sum_map_congr
    (fun b => 9*(SubexpBlockAssembly.encodeBlock b).length+SubexpBlockAssembly.blockSteps zero one b+9)
    (fun b => 9*(SubexpBlockAssembly.encodeBlock b).length+SubexpBlockAssembly.blockSteps zero one b+9)
    h (fun _ _ he => by rw [block_encoded_length he,block_steps_eq zero one he])
  simp only [SubexpBlockAssembly.assemblySteps,hs,assembled_length_eq zero one h]

end SubexponentialSAT.SubexpMomentSourceShape

end OAI.Algorithms
