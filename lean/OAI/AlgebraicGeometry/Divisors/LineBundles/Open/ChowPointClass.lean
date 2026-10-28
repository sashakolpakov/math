import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Chow Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine open Chow restriction on arbitrary finite point cycles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
    (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem openRestriction_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) =
      Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (i ≫ f) d (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext x
  rfl

variable [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f]

theorem openChowRestriction_pointClass (d : ℕ) (z : X →₀ ℚ) :
    ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d
      (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d
      (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (i ≫ f) d (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn))
  rw [openRestriction_dimensionComponent]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass.BundleCycles
