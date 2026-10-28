import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingInput

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The only untouched destinations needed by packing after the frontend. -/
def PackingSpare (a : Data) : Prop :=
  a.stacks 684=[] ∧ a.stacks 133=[] ∧ a.stacks 135=[] ∧ a.stacks 136=[] ∧
    ∀ i,a.stacks (LayoutMasters.high i)=[]

theorem cleanWork_packingSpare (a : Data) (hc : CleanWork a) : PackingSpare a := by
  refine ⟨hc _ (by decide) (by decide),hc _ (by decide) (by decide),
    hc _ (by decide) (by decide),hc _ (by decide) (by decide),?_⟩
  intro i
  apply hc
  · intro h
    have hi := i.isLt
    simp [Protected,LayoutMasters.high,Fin.ext_iff] at h
    omega
  · intro h
    have hi := congrArg Fin.val h
    simp [LayoutMasters.high] at hi
    omega

theorem packing_empty (a : Data) (hz : LeafQueryFrontend.emptyRange a 417 680)
    (hs : PackingSpare a) : PackingCallerProgram.Empty a := by
  refine ⟨?_,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2⟩
  intro i
  change a.stacks (PackingCallerProgram.Wide.ports i)=[]
  apply hz
  · simp only [PackingCallerProgram.Wide.ports_val]
    omega
  · have hi := i.isLt
    simp only [PackingCallerProgram.Wide.ports_val]
    omega

/-- Frontend output placement leaves the packing destinations untouched. -/
theorem packingSpare_of_frontend_frame (a b : Data) (hs : PackingSpare a)
    (hf : ∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
      (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i) : PackingSpare b := by
  have he (i : Fin 768) (hi : i∈([684,133,135,136] : List (Fin 768))) :
      b.stacks i=a.stacks i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;>
      exact hf _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  refine ⟨(he _ (by simp)).trans hs.1,(he _ (by simp)).trans hs.2.1,
    (he _ (by simp)).trans hs.2.2.1,(he _ (by simp)).trans hs.2.2.2.1,?_⟩
  intro i
  have hi := i.isLt
  have hh : b.stacks (LayoutMasters.high i)=a.stacks (LayoutMasters.high i) := by
    apply hf
    · right; simp [LayoutMasters.high]; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro h; have hv := congrArg Fin.val h; simp [LayoutMasters.high] at hv; omega
    · intro j h
      have hv := congrArg Fin.val h
      fin_cases j <;> simp [Exports.destination,LayoutMasters.high] at hv <;> omega
  exact hh.trans (hs.2.2.2.2 i)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
