import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass

/-! # Iso Open Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoOpenChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual open restriction and closed pushforward are inverse for a scheme isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (e : X ≅ Y) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem schemeIso_closed_open_chow (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Closed.ChowPushforward.BundleCycles.closedChowPushforward e.hom f d (Open.ChowRestriction.BundleCycles.openChowRestriction e.hom f d a) = a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass,
    Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ f d)
  exact Finsupp.mapDomain_comapDomain e.hom e.hom.isOpenEmbedding.injective _
    (fun _ _ => e.hom.homeomorph.surjective _)

theorem schemeIso_open_closed_chow (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ (e.hom ≫ f) d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction e.hom f d (Closed.ChowPushforward.BundleCycles.closedChowPushforward e.hom f d a) = a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (e.hom ≫ f) d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (e.hom ≫ f) d z, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ (e.hom ≫ f) d)
  exact Finsupp.comapDomain_mapDomain e.hom e.hom.isOpenEmbedding.injective _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoOpenChow.BundleCycles
