import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowClosedSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowPowerComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection

/-! # Generators Closed -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsClosed.BundleCycles

noncomputable section

/-! The actual projective Chow generators respect pushforward
from a closed base and its cartesian inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [E'.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsClosedImmersion i] [IsClosedImmersion j]
    (hs : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

theorem projectiveChowComponent_closedPushforward (d k n : ℕ) (hd : k + r = d + n)
    (α : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) k) :
    Filtration.BundleCycles.projectiveChowComponent p f r hp L d k n hd (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f k α) =
      Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ (i ≫ f)) (p ≫ f)
        (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d
        (Filtration.BundleCycles.projectiveChowComponent q (i ≫ f) r hq (L.pullback j) d k n hd α) := by
  change LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d n
    (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp k
      (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f k α))) = _
  rw [AffineSource.ChowClosedSquare.BundleCycles.affineSpaceSourceChowExtension_closedPushforward p q i j hs f r hp hq,
    ChowPowerComposition.BundleCycles.closedChowPushforwardOver_reindex,
    ← LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed j,
    ← LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection j,
    LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed j]
  rfl

include hs in
theorem projectiveChowGenerated_closedPushforward (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ (q ≫ (i ≫ f)) d)
    (hα : α ∈ Filtration.BundleCycles.projectiveChowGenerated q (i ≫ f) r hq (L.pullback j) d) :
    Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ (i ≫ f)) (p ≫ f)
      (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d α ∈ Filtration.BundleCycles.projectiveChowGenerated p f r hp L d := by
  induction hα using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, n, hn, hd, β, rfl⟩ := ha
    rw [← projectiveChowComponent_closedPushforward p q i j hs f r hp hq L]
    exact Filtration.BundleCycles.projectiveChowComponent_mem_generated p f r hp L d k n hn hd _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb ia ib => rw [map_add]; exact Submodule.add_mem _ ia ib
  | smul c a ha ia => rw [map_smul]; exact Submodule.smul_mem _ c ia

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsClosed.BundleCycles
