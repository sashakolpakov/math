import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass

/-! # Symmetric Projective Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChow.BundleCycles

noncomputable section

/-! Genuine Chow pullback for the actual projective symmetric spectrum
of a finite free module, with its fiber-generic cycle formula. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] [Nonempty ι] (b : Module.Basis ι R M)
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def freeSymmetricProjectiveChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M ≫ f) (d + (Nat.card ι - 1)) := by
  let : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceCharts b).smooth
  let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
  exact AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f (Nat.card ι - 1)
    (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank b) d

theorem freeSymmetricProjectiveChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    freeSymmetricProjectiveChowExtension b f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      letI : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
      DimensionChow.BundleCycles.dimensionCycleToChowQ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M ≫ f) (d + (Nat.card ι - 1))
        (AffineSpace.SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f (Nat.card ι - 1)
          (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank b) d z) := rfl

theorem freeSymmetricProjectiveChowExtension_pointClass (d : ℕ) (z : Spec (.of R) →₀ ℚ) :
    freeSymmetricProjectiveChowExtension b f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      letI : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
      Point.CycleChow.BundleCycles.pointCycleToChowQ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M ≫ f) (d + (Nat.card ι - 1))
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) z) := by
  let : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceCharts b).smooth
  let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
  exact AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f (Nat.card ι - 1)
    (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank b) d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChow.BundleCycles
