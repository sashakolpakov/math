import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSchema

namespace OAI.Algorithms

/-! The physical Cartesian enumeration contains exactly one whole attained
bucket per head, in head order, and contains every such choice. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram

open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput)

def ChoicesFor (tables : List HeadTable) (heads : List HeadInput) : Prop :=
  List.Forall₂ (fun table head => head ∈ table.choices) tables heads

theorem mem_choices (table : HeadTable) (head : HeadInput) :
    head ∈ table.choices ↔ ∃ b ∈ table.buckets,
      head = (⟨table.mask,table.context,b.2⟩ : HeadInput) := by
  simp only [HeadTable.choices,List.mem_reverse,List.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    exact ⟨b,hb,he.symm⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨b,hb,he.symm⟩

theorem mem_extend (rows : List (List HeadInput)) (choices : List HeadInput)
    (row : List HeadInput) :
    row ∈ extend rows choices ↔
      ∃ old ∈ rows, ∃ head ∈ choices, row = old ++ [head] := by
  simp only [extend,List.mem_reverse,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨old,hold,head,hhead,he⟩
    exact ⟨old,hold,head,hhead,he.symm⟩
  · rintro ⟨old,hold,head,hhead,he⟩
    exact ⟨old,hold,head,hhead,he.symm⟩

theorem mem_enumerateFrom (tables : List HeadTable) (rows : List (List HeadInput))
    (row : List HeadInput) :
    row ∈ enumerateFrom tables rows ↔
      ∃ priorHeads ∈ rows, ∃ newHeads, ChoicesFor tables newHeads ∧ row = priorHeads ++ newHeads := by
  induction tables generalizing rows with
  | nil =>
      constructor
      · intro hr
        exact ⟨row,hr,[],List.Forall₂.nil,by simp⟩
      · rintro ⟨priorHeads,hprefix,newHeads,hchoices,he⟩
        cases hchoices
        simp only [List.append_nil] at he
        exact he.symm ▸ hprefix
  | cons table tables ih =>
      rw [enumerateFrom,ih]
      constructor
      · rintro ⟨extended,hextended,newHeads,hchoices,he⟩
        obtain ⟨priorHeads,hprefix,head,hhead,rfl⟩ :=
          (mem_extend rows table.choices extended).mp hextended
        refine ⟨priorHeads,hprefix,head::newHeads,List.Forall₂.cons hhead hchoices,?_⟩
        simpa [List.append_assoc] using he
      · rintro ⟨priorHeads,hprefix,newHeads,hchoices,he⟩
        cases hchoices with
        | cons hhead htail =>
            rename_i chosen remaining
            refine ⟨priorHeads ++ [chosen],?_,remaining,htail,?_⟩
            · exact (mem_extend rows table.choices _).mpr
                ⟨priorHeads,hprefix,chosen,hhead,rfl⟩
            · simpa [List.append_assoc] using he

theorem mem_enumerate (tables : List HeadTable) (heads : List HeadInput) :
    heads ∈ enumerate tables ↔ ChoicesFor tables heads := by
  rw [enumerate,mem_enumerateFrom]
  constructor
  · rintro ⟨priorHeads,hprefix,newHeads,hchoices,he⟩
    have hp : priorHeads = [] := by simpa using hprefix
    subst priorHeads
    simp only [List.nil_append] at he
    exact he.symm ▸ hchoices
  · intro hc
    exact ⟨[],by simp,heads,hc,by simp⟩

theorem enumerate_head_count (tables : List HeadTable) (heads : List HeadInput)
    (hheads : heads ∈ enumerate tables) : heads.length = tables.length := by
  exact ((mem_enumerate tables heads).mp hheads).length_eq.symm

end SubexponentialSAT.SqrtLog.BucketTupleProgram

end OAI.Algorithms
