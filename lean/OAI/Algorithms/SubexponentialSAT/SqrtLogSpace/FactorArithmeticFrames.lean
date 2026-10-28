import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBase

/-! Register footprints of the original concrete factor arithmetic commands. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
open OAI BitProgram StructuredCalls SqrtLog.LeafProgram
open CommandRegisterFrames

private theorem not_mem_union {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} (hl : i ∉ left) (hr : i ∉ right) :
    i ∉ left ∪ right := by
  simpa only [Finset.mem_union, not_or] using And.intro hl hr

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val) (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro he
  subst i
  omega

private theorem outside8 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 8, j.castAdd 32 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

theorem clear_not_mem_writes (src : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (Factor.clear src) :=
  not_mem_clearProgram src 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

theorem move_not_mem_writes (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (Factor.move src dst) := by
  change i ∉ programWrites (StackRoutines.copyProgram src dst 159 0 1) ∪ writes (Factor.clear src)
  exact not_mem_union (not_mem_copyProgram src dst 159 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)))
    (clear_not_mem_writes src i hi)

theorem accumulate_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes Factor.accumulate := by
  have hm : i ∉ writes Factor.multiply :=
    not_mem_liftProgram _ _ _ i (outside8 i hi)
  simp only [Factor.accumulate, writes]
  exact not_mem_union (move_not_mem_writes _ _ i hi)
    (not_mem_union (move_not_mem_writes _ _ i hi)
      (not_mem_union hm (move_not_mem_writes _ _ i hi)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
