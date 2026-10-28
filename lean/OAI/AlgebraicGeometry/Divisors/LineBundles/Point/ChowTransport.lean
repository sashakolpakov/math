import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow

/-! # Chow Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual point-cycle classes respect the dimension inclusion and structure-map transport -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]

theorem dimensionChowTransport_pointCycle {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (h : f = g) (d : ℕ) (z : X →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionChowTransport h d (CycleChow.BundleCycles.pointCycleToChowQ f d z) = CycleChow.BundleCycles.pointCycleToChowQ g d z := by
  subst g
  rfl

theorem pointCycleToChowQ_inclusion (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    CycleChow.BundleCycles.pointCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) = DimensionChow.BundleCycles.dimensionCycleToChowQ f d z := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.comapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d)
    (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn) = _
  exact congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ f d)
    (Finsupp.comapDomain_mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport.BundleCycles
