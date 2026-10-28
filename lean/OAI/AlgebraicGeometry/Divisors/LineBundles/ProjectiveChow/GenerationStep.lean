import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.HyperplaneGenerators
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSourceChowLocalization

/-! # Generation Step -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationStep.BundleCycles

noncomputable section

/-! Actual Chow localization and the Cartier hyperplane formula
give the induction step for projective Chow generation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [E.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hreg : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback s).sheaf ≅ L.sheaf)
    (ι : Type) [Finite ι] (hr : Nat.card ι = r + 1)
    (j : AffineSpace ι X ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = (AffineSpace ι X ↘ X))
    (hs : Set.range s = (Set.range j)ᶜ)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ ((s ≫ p) ≫ f) d), α ∈ Filtration.BundleCycles.projectiveChowGenerated (s ≫ p) f r hq L d)

include e hr hj hs hgen in
theorem projectiveChowGeneration_cartier_step (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    α ∈ Filtration.BundleCycles.projectiveChowGenerated p f (r + 1) hp (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) d := by
  have hinfty (m : ℕ) (β : DimensionChow.BundleCycles.DimensionChowQ (s ≫ (p ≫ f)) m) :
      Closed.ChowPushforward.BundleCycles.closedChowPushforward s (p ≫ f) m β ∈
        Filtration.BundleCycles.projectiveChowGenerated p f (r + 1) hp (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) m := by
    have H := HyperplaneGenerators.BundleCycles.projectiveChowGenerated_hyperplane p s hreg f r hp hq L e m
      (DimensionChow.BundleCycles.dimensionChowTransport (Category.assoc s p f).symm m β) (hgen m _)
    rwa [DimensionChowTransportLaws.BundleCycles.closedChowPushforwardOver_transport] at H
  by_cases hd : r + 1 ≤ d
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + (r + 1) := ⟨d - (r + 1), by omega⟩
    obtain ⟨c, β, hα⟩ := AffineSourceChowLocalization.BundleCycles.affineSourceChow_decomposition_rank p f ι (r + 1) hr hp j hj s hs k α
    rw [hα]
    exact Submodule.add_mem _
      (Filtration.BundleCycles.affineSpaceSourceChowExtension_mem_projectiveGenerated p f (r + 1) hp (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) k c)
      (hinfty _ β)
  · obtain ⟨β, hβ⟩ := AffineSourceChowLocalization.BundleCycles.affineSourceChow_from_complement_below_rank p f ι j hj s hs d (by omega) α
    rw [← hβ]
    exact hinfty d β

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationStep.BundleCycles
