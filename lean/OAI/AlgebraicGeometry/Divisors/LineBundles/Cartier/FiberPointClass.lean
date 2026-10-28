import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Fiber Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.FiberPointClass.BundleCycles

noncomputable section

/-! # LineBundleCycles: the constructed fiber class agrees with restriction of the actual point intersection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme} [AlgebraicGeometry.IsNoetherian X] (j : Z ⟶ X) [IsClosedImmersion j]
    (a : Γ(X, ⊤)) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem principalCartierFiberCycleMap_eq_lift (d : ℕ) :
    Principal.CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d =
      (Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d).comp (Principal.CartierFiber.BundleCycles.principalCartierAmbientCycleMap a f d) := by
  apply Finsupp.lhom_ext
  intro x q
  change Finsupp.linearCombination ℚ (Principal.CartierFiber.BundleCycles.principalCartierFiberCycle j a f d) (Finsupp.single x q) =
    Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d
      (Finsupp.linearCombination ℚ (Principal.CartierFiber.BundleCycles.principalCartierGradedCycle a f d) (Finsupp.single x q))
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
  rfl

variable [AlgebraicGeometry.IsNoetherian Z] [LocallyOfFiniteType f]

theorem principalCartierFiberClassMap_eq_pointClass (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    Principal.CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d z =
      Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
        (Principal.CartierFiber.BundleCycles.principalCartierPointMap a (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) z)) := by
  rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap_graded, Point.CycleChow.BundleCycles.closedPointCycleToChowQ_graded]
  apply congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d)
  exact LinearMap.congr_fun (principalCartierFiberCycleMap_eq_lift j a f d) z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.FiberPointClass.BundleCycles
