import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramExportFacts

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem export_sep : ∀ p∈exportPairs,∀ q∈exportPairs,p.1≠q.2 := by
  intro p hp q hq
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> decide

theorem export_targets (a : Local) (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[])
    (h136 : a.stacks 136=[]) : ∀ p∈exportPairs,a.stacks p.2=[] := by
  simp only [exportPairs,List.mem_cons,List.not_mem_nil,or_false]
  rintro p (rfl|rfl|rfl) <;> assumption

theorem exported_wordBound (a : Local) (B : ℕ) (h : WordBound B a)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[]) :
    WordBound B (exported a) :=
  clearMany_wordBound privatePorts _ B (copyMany_wordBound exportPairs a B (by decide)
    (export_targets a h133 h135 h136) export_sep h)

theorem finishCost_le (a : Local) (B : ℕ) (h : WordBound B a)
    (h133 : a.stacks 133=[]) (h135 : a.stacks 135=[]) (h136 : a.stacks 136=[])
    (hz : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[]) :
    finishCost a+1 ≤ 1000*(B+1) := by
  have hc := copyManyCost_le exportPairs a B export_sep (fun p hp=>h p.1)
  have hw := copyMany_wordBound exportPairs a B (by decide)
    (export_targets a h133 h135 h136) export_sep h
  have hd := clearManyCost_le privatePorts _ B hw
  have hp := LeafProgram.LayoutMasters.parkCost_le (exported a) B
    (exported_wordBound a B h h133 h135 h136) (by intro i; rw [exported_high,hz])
  change copyManyCost exportPairs a ≤ 3*(7*B+5) at hc
  change clearManyCost privatePorts (copyManyState exportPairs a) ≤ 64*(2*B+3) at hd
  unfold finishCost exportCost
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
