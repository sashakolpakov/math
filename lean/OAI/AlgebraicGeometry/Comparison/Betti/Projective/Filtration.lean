import OAI.AlgebraicGeometry.Comparison.Betti.HodgeBidegreeIndex
import OAI.Analysis.HodgeTheory.Decomposition.Constructions

/-! # Filtration -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Filtration

noncomputable section

/-!
BettiComparison's independent Betti filtration is the image of closed filtered smooth
forms. The full Hodge decomposition used here is the proved HodgeDecomposition theorem.
This identifies the Betti side only; algebraic filtration compatibility still
requires the proper algebraic-to-holomorphic hypercohomology comparison.
-/

/-- The explicit boundary cases in BettiComparison agree with the sum of pure pieces. -/
theorem projectiveBettiHodgeFiltration_eq_hodgeSum
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    Target.projectiveBettiHodgeFiltration P n r =
      ⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (_ : r ≤ (i.val.1 : ℤ)),
        Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P n i := by
  unfold Target.projectiveBettiHodgeFiltration
  split_ifs with h0 hn
  · have htop :=
      (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration P n).1.submodule_iSup_eq_top
    rw [← htop]
    congr 1
    funext i
    rw [iSup_pos (show r ≤ (i.val.1 : ℤ) by omega)]
  · symm
    apply le_antisymm
    · refine iSup_le fun i => iSup_le fun hi => ?_
      have := i.property
      omega
    · exact bot_le
  · exact HodgeBidegreeIndex.projectivePureBetti_iSup_eq_hodgePiece_iSup P n r

/-- The independently defined BettiComparison Betti filtration is exactly the image of
closed smooth forms with holomorphic degree at least `r`. -/
theorem projectiveBettiHodgeFiltration_eq_closedSmoothFiltration
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (r : ℤ) :
    Target.projectiveBettiHodgeFiltration P n r =
      Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti P n r := by
  rw [projectiveBettiHodgeFiltration_eq_hodgeSum]
  exact ((Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration P n).2.2 r).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Filtration
