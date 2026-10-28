import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Chow To Projective Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ChowToProjectiveChow.BundleCycles

noncomputable section

/-! Extracting a projective codimension component descends from
every actual dimension-graded Chow group. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p d : ℕ)

theorem dimensionRelations_projectivePointClass :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ X.structureMap d ≤
      LinearMap.ker ((Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p).comp (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d)) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  change Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p
    (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.structureMap d W g)) = 0
  rw [Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push X.structureMap d W hW]
  exact Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass_principal X p W g hg

def dimensionChowToProjectiveChow : DimensionChow.BundleCycles.DimensionChowQ X.structureMap d →ₗ[ℚ] Chow.BundleCycles.ChowQ X p :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ X.structureMap d).liftQ
    ((Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p).comp (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d))
    (dimensionRelations_projectivePointClass X p d)

theorem dimensionChowToProjectiveChow_cycle (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.structureMap d →₀ ℚ) :
    dimensionChowToProjectiveChow X p d (DimensionChow.BundleCycles.dimensionCycleToChowQ X.structureMap d z) =
      Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d z) := rfl

theorem dimensionChowToProjectiveChow_pointClass (z : X.carrier →₀ ℚ) :
    dimensionChowToProjectiveChow X p d (Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d z) =
      Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d
        (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent X.structureMap d z)) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ChowToProjectiveChow.BundleCycles
