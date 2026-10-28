import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramExport

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem copyMany_congr {S : ℕ} (ps : List (Fin S × Fin S)) (a b : State 16 S)
    (h : a.stacks=b.stacks) :
    (copyManyState ps a).stacks=(copyManyState ps b).stacks ∧
    copyManyCost ps a=copyManyCost ps b := by
  induction ps generalizing a b with
  | nil => exact ⟨h,rfl⟩
  | cons p ps ih =>
    have hs : (copyState p.1 p.2 a).stacks=(copyState p.1 p.2 b).stacks := by simp only [copyState_stack,h]
    obtain ⟨h1,h2⟩ := ih _ _ hs
    exact ⟨h1,by simp only [copyManyCost,h,h2]⟩

theorem clearMany_congr {S : ℕ} (ps : List (Fin S)) (a b : State 16 S)
    (h : a.stacks=b.stacks) :
    (clearManyState ps a).stacks=(clearManyState ps b).stacks ∧
    clearManyCost ps a=clearManyCost ps b := by
  induction ps generalizing a b with
  | nil => exact ⟨h,rfl⟩
  | cons p ps ih =>
    have hs : (clearState p a).stacks=(clearState p b).stacks := by simp only [clearState,h]
    obtain ⟨h1,h2⟩ := ih _ _ hs
    exact ⟨h1,by simp only [clearManyCost,h,h2]⟩

theorem finish_congr (a b : Local) (h : a.stacks=b.stacks) :
    (finished a).stacks=(finished b).stacks ∧ finishCost a=finishCost b := by
  obtain ⟨hc,hct⟩ := copyMany_congr exportPairs a b h
  obtain ⟨he,het⟩ := clearMany_congr privatePorts _ _ hc
  change (exported a).stacks=(exported b).stacks at he
  obtain ⟨hp,hpt⟩ := copyMany_congr LeafProgram.LayoutMasters.parkPairs _ _ he
  obtain ⟨hf,hft⟩ := clearMany_congr LeafProgram.LayoutMasters.lowPorts _ _ hp
  exact ⟨hf,by simp only [finishCost,exportCost,LeafProgram.LayoutMasters.parkCost,hct,het,hpt,hft]⟩

theorem finished_frame (a : Local) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (hl : i.val < 128 ∨ 142 ≤ i.val)
    (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (finished a).stacks i=a.stacks i := by
  rw [finished,parked_frame _ i hl hh]
  apply exported_frame a i hb <;> intro h <;> subst i <;> norm_num at hl

theorem finished_bank (a : Local) (i : Fin 64) : (finished a).stacks (ports i)=[] := by
  rw [finished,parked_frame,exported_bank]
  · right; change 142 ≤ 417+i.val; omega
  · left; change 417+i.val < 730; have := i.isLt; omega

theorem finished_low (a : Local) (i : Fin 14) :
    (finished a).stacks (LeafProgram.LayoutMasters.low i)=[] :=
  LeafProgram.LayoutMasters.parked_low _ i

theorem exported_high (a : Local) (i : Fin 14) :
    (exported a).stacks (LeafProgram.LayoutMasters.high i)=a.stacks (LeafProgram.LayoutMasters.high i) := by
  apply exported_frame
  · right; change 481 ≤ 730+i.val; omega
  all_goals intro h; have hv := congrArg Fin.val h; simp [LeafProgram.LayoutMasters.high] at hv; omega

theorem finished_high (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (i : Fin 14) :
    (finished a).stacks (LeafProgram.LayoutMasters.high i)=
      (exported a).stacks (LeafProgram.LayoutMasters.low i) := by
  apply LeafProgram.LayoutMasters.parked_high
  intro j
  rw [exported_high,hz]

theorem finished_words (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 735=a.stacks (ports 62) := by
  rw [show (735 : Fin 768)=LeafProgram.LayoutMasters.high 5 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 62,133) (by simp [exportPairs])

theorem finished_metadata (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 737=a.stacks (ports 63) := by
  rw [show (737 : Fin 768)=LeafProgram.LayoutMasters.high 7 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 63,135) (by simp [exportPairs])

theorem finished_plans (a : Local) (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[])
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    (finished a).stacks 738=a.stacks (ports 61) := by
  rw [show (738 : Fin 768)=LeafProgram.LayoutMasters.high 8 from rfl,finished_high a hz]
  exact exported_value a h133 h135 h136 (ports 61,136) (by simp [exportPairs])

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
