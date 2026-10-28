import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Exporting and parking never enlarge an individual data word: every
destination is empty, and the private and low banks are subsequently erased. -/
theorem result_wordBound (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    WordBound B (result a p w tail) := by
  have hm := middle_wordBound a p w tail B ha hb
  have hx := Wide.exported_wordBound (middle a p w tail) B hm
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans)
  apply clearMany_wordBound LeafProgram.LayoutMasters.lowPorts _ B
  apply copyMany_wordBound LeafProgram.LayoutMasters.parkPairs _ B
    LeafProgram.LayoutMasters.park_nodup ?_ LeafProgram.LayoutMasters.park_sep hx
  intro q hq
  simp only [LeafProgram.LayoutMasters.parkPairs,List.mem_map,List.mem_finRange,true_and] at hq
  obtain ⟨i,rfl⟩ := hq
  rw [Wide.exported_high,middle_parked a p he w tail i]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
