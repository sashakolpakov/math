import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleLift

/-! # Cycle Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow.BundleCycles

noncomputable section

/-!
# LineBundleCycles: taking the dimension grade and Chow class of an actual point cycle
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]

def pointCycleToChowQ (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) : (X →₀ ℚ) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionCycleToChowQ f d).comp
    (Finsupp.lcomapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective)

theorem pointCycleToChowQ_principal (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    pointCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) = 0 :=
  Principal.CartierCycle.BundleCycles.dimensionCycleToChowQ_principal_any f d W hW g

def closedPointCycleToChowQ (j : Z ⟶ X) [IsClosedImmersion j] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    (X →₀ ℚ) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d :=
  (pointCycleToChowQ (j ≫ f) d).comp (Finsupp.lcomapDomain j j.isClosedEmbedding.injective)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem closedPointCycleToChowQ_pushforward (j : Z ⟶ X) [IsClosedImmersion j]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (z : Z →₀ ℚ) :
    closedPointCycleToChowQ j f d (Finsupp.mapDomain j z) = pointCycleToChowQ (j ≫ f) d z := by
  change pointCycleToChowQ (j ≫ f) d
    (Finsupp.comapDomain j (Finsupp.mapDomain j z) j.isClosedEmbedding.injective.injOn) = _
  exact congrArg (pointCycleToChowQ (j ≫ f) d)
    (Finsupp.comapDomain_mapDomain j j.isClosedEmbedding.injective z)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem closedPointCycleToChowQ_graded (j : Z ⟶ X) [IsClosedImmersion j]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    closedPointCycleToChowQ j f d (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d (Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d z) := by
  apply congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d)
  ext q
  exact Open.CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply f d z (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f d q)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow.BundleCycles
