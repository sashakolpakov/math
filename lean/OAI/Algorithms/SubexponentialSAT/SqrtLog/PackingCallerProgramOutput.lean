import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem result_frame (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 768)
    (hb : i.val < 417 ∨ 481 ≤ i.val) (hl : i.val < 128 ∨ 142 ≤ i.val)
    (hh : i.val < 730 ∨ 744 ≤ i.val) :
    (result a p w tail).stacks i=a.stacks i := by
  rw [result,Wide.finished_frame _ _ hb hl hh,middle_frame _ _ _ _ _ hb]

theorem result_bank (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    (result a p w tail).stacks (Wide.ports i)=[] := Wide.finished_bank _ i

theorem result_low (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 14) :
    (result a p w tail).stacks (LeafProgram.LayoutMasters.low i)=[] := Wide.finished_low _ i

theorem middle_parked (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 14) :
    (middle a p w tail).stacks (LeafProgram.LayoutMasters.high i)=[] := by
  rw [middle_frame]
  · exact he.parked i
  · right; change 481 ≤ 730+i.val; omega

theorem result_words (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 735=((p.words w tail).map ReadPlan.encodeWord).flatten := by
  rw [result,Wide.finished_words _ (middle_parked a p he w tail)]
  · exact middle_words a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

theorem result_metadata (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 737=(p.spec w tail).suffix.metadata := by
  rw [result,Wide.finished_metadata _ (middle_parked a p he w tail)]
  · exact middle_metadata a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

theorem result_plans (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (result a p w tail).stacks 738=planBits p.scopes p.n p.mask := by
  rw [result,Wide.finished_plans _ (middle_parked a p he w tail)]
  · exact middle_plans a p w tail
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata
  · rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans

theorem result_parameter (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin 14) (h5 : i≠5) (h7 : i≠7) (h8 : i≠8) :
    (result a p w tail).stacks (LeafProgram.LayoutMasters.high i)=
      a.stacks (LeafProgram.LayoutMasters.low i) := by
  rw [result,Wide.finished_high _ (middle_parked a p he w tail)]
  have hb : (LeafProgram.LayoutMasters.low i).val < 417 ∨
      481 ≤ (LeafProgram.LayoutMasters.low i).val := by
    left; change 128+i.val < 417; have := i.isLt; omega
  rw [Wide.exported_frame _ _ hb,middle_frame _ _ _ _ _ hb]
  all_goals intro h; apply_assumption; apply Fin.ext
            have hv := congrArg Fin.val h
            simp [LeafProgram.LayoutMasters.low] at hv ⊢
            omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
