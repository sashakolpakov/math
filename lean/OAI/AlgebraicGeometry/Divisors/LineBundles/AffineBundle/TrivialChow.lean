import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.TrivializedAffineSpaceChow

/-! # Trivial Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.TrivialChow.Cycles

noncomputable section

/-! # LineBundleCycles: the canonical bundle Chow map is bijective on an actual global trivialization -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSpaceTrivialization_hasChartsOfRank {E X : Scheme.{0}} (p : E ⟶ X)
    (ι : Type) [Finite ι] (e : AffineSpace ι X ≅ E) (he : e.hom ≫ p = (AffineSpace ι X ↘ X)) :
    LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p (Nat.card ι) := by
  intro x
  refine ⟨X, 𝟙 X, ι, inferInstance, e.hom, inferInstance, inferInstance, ⟨x, rfl⟩, ?_, rfl⟩
  exact IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, he]⟩

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (ι : Type) [Finite ι]
    (h : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p (Nat.card ι))
    (e : AffineSpace ι X ≅ E) (he : e.hom ≫ p = (AffineSpace ι X ↘ X))

theorem affineBundleChowExtension_eq_trivialization (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    ChowExtension.Cycles.affineBundleChowExtension p f (Nat.card ι) h d a =
      TrivializedAffineSpaceChow.BundleCycles.trivializedAffineSpaceChowEquiv X f p ι e he d a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, ChowPointClass.Cycles.affineBundleChowExtension_pointClass,
    TrivializedAffineSpaceChow.BundleCycles.trivializedAffineSpaceChowEquiv_pointClass]

include e he in
theorem affineBundleChowExtension_trivial_bijective (d : ℕ) :
    Function.Bijective (ChowExtension.Cycles.affineBundleChowExtension p f (Nat.card ι) h d) := by
  have hh : (ChowExtension.Cycles.affineBundleChowExtension p f (Nat.card ι) h d : DimensionChow.BundleCycles.DimensionChowQ f d →
      DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι)) = TrivializedAffineSpaceChow.BundleCycles.trivializedAffineSpaceChowEquiv X f p ι e he d :=
    funext (affineBundleChowExtension_eq_trivialization p f ι h e he d)
  rw [hh]
  exact (TrivializedAffineSpaceChow.BundleCycles.trivializedAffineSpaceChowEquiv X f p ι e he d).bijective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.TrivialChow.Cycles
