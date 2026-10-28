import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowReindex
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOpenPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange

/-! # Generators Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsOpen.BundleCycles

noncomputable section

/-! Actual projective Chow generators commute with open restriction,
and every generated class on an open lifts to a generated global class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [E'.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

theorem projectiveChowComponent_openRestriction (d k n : ℕ) (hd : k + r = d + n)
    (α : DimensionChow.BundleCycles.DimensionChowQ f k) :
    DimensionChow.BundleCycles.dimensionChowTransport (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d (Filtration.BundleCycles.projectiveChowComponent p f r hp L d k n hd α)) =
      Filtration.BundleCycles.projectiveChowComponent q (i ≫ f) r hq (L.pullback j) d k n hd (Open.ChowRestriction.BundleCycles.openChowRestriction i f k α) := by
  change DimensionChow.BundleCycles.dimensionChowTransport (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d
    (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d n
      (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp k α)))) = _
  rw [LineBundle.ChowOpenPower.Cycles.separatedLineBundleChowPower_open, LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_transport,
    ← Open.ChowReindex.BundleCycles.openChowRestriction_reindex, Open.ChowReindex.BundleCycles.dimensionChowTransport_reindex,
    AffineSource.ChowOpenSquare.BundleCycles.affineSpaceSourceChowExtension_openSquare p q i j hs.w f r hp hq]
  rfl

theorem projectiveChowGenerated_openRestriction_lift (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ (q ≫ (i ≫ f)) d)
    (hα : α ∈ Filtration.BundleCycles.projectiveChowGenerated q (i ≫ f) r hq (L.pullback j) d) :
    ∃ γ : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d, γ ∈ Filtration.BundleCycles.projectiveChowGenerated p f r hp L d ∧
      DimensionChow.BundleCycles.dimensionChowTransport (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d
        (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d γ) = α := by
  induction hα using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, n, hn, hd, β, rfl⟩ := ha
    obtain ⟨β', hβ⟩ := Open.ChowRestriction.BundleCycles.openChowRestriction_surjective i f k β
    refine ⟨Filtration.BundleCycles.projectiveChowComponent p f r hp L d k n hd β',
      Filtration.BundleCycles.projectiveChowComponent_mem_generated p f r hp L d k n hn hd β', ?_⟩
    rw [projectiveChowComponent_openRestriction p q i j hs f r hp hq L, hβ]
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
  | add a b ha hb ia ib =>
    obtain ⟨γ, hγ, eγ⟩ := ia
    obtain ⟨δ, hδ, eδ⟩ := ib
    exact ⟨γ + δ, Submodule.add_mem _ hγ hδ, by rw [map_add, map_add, eγ, eδ]⟩
  | smul c a ha ia =>
    obtain ⟨γ, hγ, eγ⟩ := ia
    exact ⟨c • γ, Submodule.smul_mem _ c hγ, by rw [map_smul, map_smul, eγ]⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsOpen.BundleCycles
