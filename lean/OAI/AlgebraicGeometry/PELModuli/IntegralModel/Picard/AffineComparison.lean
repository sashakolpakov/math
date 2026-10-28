import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover

/-! # Affine Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.AffineComparison.PicardAffineComparison

noncomputable section

/-! An fppf covering family of actual line-bundle comparisons gives one
actual comparison over an affine fpqc cover of the parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OverFiniteFppfCover

variable {S : Scheme.{u}} (P : Over S) {T : Over S}
  [CompactSpace T.left]
  (L M : (T ⊗ P).left.Modules)
  (R : (Scheme.fppfTopology.over S).Cover T)
  (e : ∀ {U : Over S} (u : U ⟶ T), R.1 u →
    ((Scheme.Modules.pullback (u ▷ P).left).obj L ≅
      (Scheme.Modules.pullback (u ▷ P).left).obj M))

def finiteCover := Isogenies.NeighborCounting.OverFiniteFppfCover.underlyingFamily R.2

theorem component_comp (i : Fin (finiteCover R).n) :
    (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i ▷ P).left ≫
        (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left =
      (Isogenies.NeighborCounting.OverFiniteFppfCover.coverMap (finiteCover R) i ▷ P).left :=
  ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).map_comp (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i)
      (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R))).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).map
      (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion_projection (finiteCover R) i))

def componentIso (i : Fin (finiteCover R).n) :
    (Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i ▷ P).left).obj
        ((Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left).obj L) ≅
      (Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i ▷ P).left).obj
        ((Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left).obj M) :=
  ((Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i ▷ P).left
        (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left ≪≫
      Scheme.Modules.pullbackCongr (component_comp P R i)).app L) ≪≫
    e (Isogenies.NeighborCounting.OverFiniteFppfCover.coverMap (finiteCover R) i) (Isogenies.NeighborCounting.OverFiniteFppfCover.coverMap_member (finiteCover R) i) ≪≫
    ((Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R) i ▷ P).left
        (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left ≪≫
      Scheme.Modules.pullbackCongr (component_comp P R i)).app M).symm

include e in
theorem exists_coverIso : Nonempty
    ((Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left).obj L ≅
      (Scheme.Modules.pullback (Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R) ▷ P).left).obj M) := by
  obtain ⟨d, _, _⟩ := ProductOpenCover.PicardProductOpenCover.existsUnique_disjoint_product_iso P
    (Isogenies.NeighborCounting.OverFiniteFppfCover.coverObject (finiteCover R)) (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion (finiteCover R))
    (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion_covers (finiteCover R)) (Isogenies.NeighborCounting.OverFiniteFppfCover.coverInclusion_disjoint (finiteCover R))
    (componentIso P L M R e)
  exact ⟨d⟩

include R e in
/-- The comparison is constructed on the coproduct of a finite affine
refinement. Its map to the original parameter is flat, surjective and
quasi-compact, including over nonreduced parameters. -/
theorem exists_affine_fpqc_comparison [QuasiSeparatedSpace T.left] :
    ∃ (U : Over S) (u : U ⟶ T), IsAffine U.left ∧ Flat u.left ∧
      Surjective u.left ∧ QuasiCompact u.left ∧ Nonempty
        ((Scheme.Modules.pullback (u ▷ P).left).obj L ≅
          (Scheme.Modules.pullback (u ▷ P).left).obj M) :=
  ⟨Isogenies.NeighborCounting.OverFiniteFppfCover.coverTotal (finiteCover R), Isogenies.NeighborCounting.OverFiniteFppfCover.coverProjection (finiteCover R),
    inferInstance, inferInstance, inferInstance, inferInstance,
    exists_coverIso P L M R e⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.AffineComparison.PicardAffineComparison
