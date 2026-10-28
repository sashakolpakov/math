import OAI.RepresentationTheory.Theta.Geometric.DominantLinePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LocalDescentGluing

/-! # Dominant Local Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.DominantLocalDescent.IntrinsicDominantPullback

noncomputable section

/-! Native local module descents glue under scheme-theoretically
dominant pullback, including the nonflat square-zero parameter map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicOpenSquare.PicardIntrinsicOpenSquare OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization.PicardOpenFactorization

variable {X Y : Scheme} (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    {M N : Y.Modules} (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)

include hN in
theorem existsUnique_hom_of_local_descent
    {ι : Type*} (U : ι → Y.Opens) (hU : (⊤ : Y.Opens) ≤ iSup U)
    (c : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hc : ∀ i,
      (Scheme.Modules.pullback (f ∣_ U i)).map (c i) ≫
          (AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).inv.app N =
        (AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).inv.app M ≫
          (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U i).ι).map q) :
    ∃! a : M ⟶ N, (Scheme.Modules.pullback f).map a = q := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have : Mono (adj.unit.app N) := DominantLinePullback.IntrinsicDominantPullback.unit_line_mono f hN
  let b := adj.homEquiv _ _ q
  let d (i) : (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N :=
    ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M).homCongr
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app N) (c i)
  have hd (i) : d i ≫ (Scheme.Modules.pullback (U i).ι).map (adj.unit.app N) =
      (Scheme.Modules.pullback (U i).ι).map b := by
    have := AlgebraicGeometry.PELModuli.IntegralModel.Picard.IntrinsicOpenSquare.PicardIntrinsicOpenSquare.canonical_rightMate_isIso f (U i)
    have he := AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization.factorization_of_square adj
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U i))
      (AlgebraicGeometry.Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f (U i)).symm q (c i) (hc i)
    exact AlgebraicGeometry.Isogenies.NeighborCounting.AdjointSquareFactorization.transport_factorization (Scheme.Modules.restrictFunctorIsoPullback (U i).ι)
      (c i) (adj.unit.app N) b he
  obtain ⟨a, ha, hu⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization.PicardOpenFactorization.existsUnique_open_factorization M (adj.unit.app N) b U hU d hd
  have he (a : M ⟶ N) : adj.homEquiv _ _ ((Scheme.Modules.pullback f).map a) = a ≫ adj.unit.app N := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  refine ⟨a, (adj.homEquiv _ _).injective ((he a).trans ha), ?_⟩
  intro a' ha'
  exact hu a' ((he a').symm.trans (congrArg (adj.homEquiv _ _) ha'))

end

end OAI.RepresentationTheory.Theta.Geometric.DominantLocalDescent.IntrinsicDominantPullback
