import OAI.AlgebraicGeometry.Divisors.LineBundles.SupportedCartierFiberRelation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.FiberPointClass

/-! # Cartier Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierChow.BundleCycles

noncomputable section

/-!
# LineBundleCycles: principal Cartier intersection on the genuine source Chow quotient
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Z] (j : Z ⟶ X) [IsClosedImmersion j]
    (a : Γ(X, ⊤)) (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hzero

theorem principalCartierFiberClassMap_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f (d + 1) W g) = 0 := by
  rw [Cartier.FiberPointClass.BundleCycles.principalCartierFiberClassMap_eq_pointClass,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f (d + 1) W (by omega)]
  exact SupportedCartierFiberRelation.BundleCycles.principalCartier_fiber_principal_zero j a hzero f d W hW g hg

theorem principalCartierFiberClassMap_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1) ≤ LinearMap.ker (CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  exact principalCartierFiberClassMap_principal j a hzero f d W (by omega) g hg

def principalCartierChowMap (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1)).liftQ (CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d)
    (principalCartierFiberClassMap_relations j a hzero f d)

@[simp]
theorem principalCartierChowMap_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    principalCartierChowMap j a hzero f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) z) =
      CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d z := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierChow.BundleCycles
