import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramClassify

namespace OAI.Algorithms

/-! Diagonal equality is already encoded by the physical compatibility scan:
compatible words with no genuinely transposed coordinate are identical. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixEntryKernel
open SubexponentialSAT.Subexp.MatrixScanProgram SubexponentialSAT.Subexp.MatrixEntryEvaluation

variable {r Q Δ : ℕ}

theorem eq_iff_compatible_transposed_zero (i : Fin Δ) (u y : UniversalType r Q Δ) :
    u = y ↔ AllCompatible i u y ∧ (allTransposed i u y).card = 0 := by
  constructor
  · rintro rfl
    refine ⟨⟨fun _ _ _ => rfl,fun _ => Or.inl rfl⟩,?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have h := (Finset.mem_filter.mp hl).2
    exact h.1 (congrArg Prod.snd h.2)
  · rintro ⟨hc,ht⟩
    apply (eq_iff_pair_spectators i u y).mpr
    refine ⟨hc.1,fun l => ?_⟩
    rcases hc.2 l with hp | hp
    · exact hp
    · by_cases hmono : u.head l = u.slot i l
      · simpa [pair,hmono] using hp
      · have hm : l ∈ allTransposed i u y := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmono,hp⟩
        rw [Finset.card_eq_zero.mp ht] at hm
        exact (Finset.notMem_empty _ hm).elim

def diagonalFromScan (a : SubexponentialSAT.Subexp.MatrixScanProgram.Data) : Bool :=
  a.regs 7 && (a.stacks 3).isEmpty

theorem result_diagonal (u y : UniversalType r Q 1)
    (a : SubexponentialSAT.Subexp.MatrixScanProgram.Data)
    (hflag : a.regs 7 = true) (h3 : a.stacks 3 = []) :
    diagonalFromScan (result (rows 0 u y) a) = decide (u = y) := by
  have hs : SpectatorsAgree (0:Fin 1) u y := by
    intro j hj
    exact (hj (Subsingleton.elim j 0)).elim
  have hc : (rows (0:Fin 1) u y).all compatible = decide (AllCompatible (0:Fin 1) u y) := by
    simpa [hs] using compatibility_rows (0:Fin 1) u y
  unfold diagonalFromScan
  rw [result_compatible,hflag,Bool.true_and,hc,result_count3,h3,List.append_nil]
  rw [transposedCount_rows]
  simp [eq_iff_compatible_transposed_zero (0:Fin 1) u y]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
