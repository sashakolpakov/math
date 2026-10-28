import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer

namespace OAI.Algorithms

/-! Physical caller ABI for per-branch high-context staging. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def regMap : Fin 4 → Fin 40 := Fin.castAdd 36
def stackMap : Fin 10 → Fin 768 := fun i => match i.val with
  | 0 => 330
  | 1 => 338
  | 2 => 702
  | 3 => 703
  | 4 => 680
  | 5 => 681
  | 6 => 682
  | 7 => 683
  | 8 => 684
  | _ => 685
theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 4 36
theorem stackMap_injective : Function.Injective stackMap := by decide

def command : Code := .call (ProgramLinking.liftProgram Local.program regMap stackMap)

def scratch : List (Fin 768) := [680,681,682,683,684,685]
def changed : List (Fin 768) := [702,703,680,681,682,683,684,685]

noncomputable def finished (a : Data) (regs : Fin 4 → Bool) (high : List Bool) : Data :=
  embedState regMap stackMap a (Local.state regs (a.stacks 330) (a.stacks 338)
    (a.stacks 338).reverse (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) high).reverse
    [] [] [] [] [] [])

@[simp] theorem finished_mask (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (finished a regs high).stacks 702 = (a.stacks 338).reverse :=
  embedState_stack regMap stackMap a _ stackMap_injective 2

@[simp] theorem finished_high (a : Data) (regs : Fin 4 → Bool) (high : List Bool) :
    (finished a regs high).stacks 703 =
      (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) high).reverse :=
  embedState_stack regMap stackMap a _ stackMap_injective 3

theorem finished_scratch (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 768) (hi : i ∈ scratch) : (finished a regs high).stacks i = [] := by
  simp only [scratch,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact embedState_stack regMap stackMap a _ stackMap_injective 4
  · exact embedState_stack regMap stackMap a _ stackMap_injective 5
  · exact embedState_stack regMap stackMap a _ stackMap_injective 6
  · exact embedState_stack regMap stackMap a _ stackMap_injective 7
  · exact embedState_stack regMap stackMap a _ stackMap_injective 8
  · exact embedState_stack regMap stackMap a _ stackMap_injective 9

theorem finished_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 768) (hi : i ∉ changed) : (finished a regs high).stacks i = a.stacks i := by
  by_cases h : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := h
    rw [show (finished a regs high).stacks (stackMap j) =
      (Local.state regs (a.stacks 330) (a.stacks 338) (a.stacks 338).reverse
        (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) high).reverse
        [] [] [] [] [] []).stacks j from
      embedState_stack regMap stackMap a _ stackMap_injective j]
    fin_cases j <;> simp_all [stackMap,changed,Local.state,Local.tapes]
  · exact embedState_stack_frame regMap stackMap a _ i h

theorem finished_register_frame (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 40) (hi : 4 ≤ i.val) : (finished a regs high).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

/-- The source premise describes the actual counter tape. The program itself
extracts the bits, rather than accepting an externally supplied high vector. -/
theorem run (a : Data) (words : List (List Bool))
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (he : ∀ i ∈ changed, a.stacks i = [])
    (hlen : words.flatten.length = HighIncidenceProgram.Restriction.highCount (a.stacks 338)) :
    ∃ n regs, n ≤ Local.cost words (a.stacks 338)+1 ∧
      Eval command n a (finished a regs words.flatten) := by
  obtain ⟨rf,hr⟩ := Local.runsIn (a.regs ∘ regMap) words (a.stacks 338) hlen
  have ha : restrictState regMap stackMap a =
      Local.state (a.regs ∘ regMap) (ProgramEncoding.encodeRecords words) (a.stacks 338)
        [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [stackMap,Local.tapes,hc,
        he 702 (by simp [changed]),he 703 (by simp [changed]),
        he 680 (by simp [changed]),he 681 (by simp [changed]),
        he 682 (by simp [changed]),he 683 (by simp [changed]),
        he 684 (by simp [changed]),he 685 (by simp [changed])]
  have hr' := Local.transport_initial _ _ ha.symm hr
  obtain ⟨n,hn,hev⟩ := lifted_call Local.program regMap stackMap regMap_injective
    stackMap_injective a _ _ hr'
  have hout : embedState regMap stackMap a
      (Local.state rf (ProgramEncoding.encodeRecords words) (a.stacks 338)
        (a.stacks 338).reverse
        (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 338) words.flatten).reverse
        [] [] [] [] [] []) = finished a rf words.flatten := by
    unfold finished
    rw [hc]
  exact ⟨n,rf,hn,Eq.mp (congrArg (fun b => Eval command n a b) hout) hev⟩

theorem run_singleton (a : Data) (words : List (List Bool)) (h : ℕ)
    (hc : a.stacks 330 = ProgramEncoding.encodeRecords words)
    (he : ∀ i ∈ changed, a.stacks i = [])
    (hshape : words.map List.length = List.replicate h 1)
    (hh : h = HighIncidenceProgram.Restriction.highCount (a.stacks 338)) :
    ∃ n regs, n ≤ 22*(a.stacks 338).length+43*h+37 ∧
      Eval command n a (finished a regs words.flatten) := by
  have hw : words.length = h := by
    have ht := congrArg List.length hshape
    simpa only [List.length_map,List.length_replicate] using ht
  have hf : words.flatten.length = h := by
    rw [List.length_flatten,hshape]
    simp
  have henc : (ProgramEncoding.encodeRecords words).length = 4*h+1 := by
    rw [show ProgramEncoding.encodeRecords words = Encoding.encodeList id words from rfl,
      ExecCNFTupleOdometer.encoded_length,hf,hw]
    omega
  obtain ⟨n,regs,hn,hev⟩ := run a words hc he (hf.trans hh)
  refine ⟨n,regs,?_,hev⟩
  unfold Local.cost at hn
  rw [henc,hf,hw] at hn
  omega

end SubexponentialSAT.SqrtLog.LeafHighContextProgram

end OAI.Algorithms
