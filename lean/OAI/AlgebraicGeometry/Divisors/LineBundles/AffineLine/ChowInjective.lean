import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CartierLeftInverse
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Injective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowInjective.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual zero-section intersection is a left inverse to affine-line Chow pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineZeroChowMap_extension (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    ZeroChow.BundleCycles.affineLineZeroChowMap X f d (ChowExtension.BundleCycles.affineLineChowExtension X f d a) = a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [ChowExtension.BundleCycles.affineLineChowExtension_cycle, ZeroChow.BundleCycles.affineLineZeroChowMap_cycle,
    Cartier.FiberPointClass.BundleCycles.principalCartierFiberClassMap_eq_pointClass, CycleGrading.BundleCycles.affineLineGradedCycleExtension_forget,
    CartierLeftInverse.BundleCycles.affineLineCartierPointMap_extension, Point.CycleChow.BundleCycles.closedPointCycleToChowQ_pushforward,
    Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion]

theorem affineLineChowExtension_injective (d : ℕ) : Function.Injective (ChowExtension.BundleCycles.affineLineChowExtension X f d) :=
  Function.LeftInverse.injective (affineLineZeroChowMap_extension X f d)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowInjective.BundleCycles
