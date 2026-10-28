import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.FiberPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction

/-! # Specialization Cycle Forgetting -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecializationCycleForgetting.BundleCycles

noncomputable section

/-! # LineBundleCycles: forgetting grades in actual closure and Cartier-fiber operations -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian X]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem openDimensionCycleExtension_forget (i : U ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension i f d z) =
      Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d z) := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ z) = Finsupp.mapDomain _ (Finsupp.mapDomain _ z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

theorem principalCartierFiberCycleMap_forget_push (j : Z ⟶ X) [IsClosedImmersion j]
    (a : Γ(X, ⊤)) (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    Finsupp.mapDomain j (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (j ≫ f) d (Principal.CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d z)) =
      Principal.CartierFiber.BundleCycles.principalCartierPointMap a (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) z) := by
  have h := LinearMap.congr_fun (Principal.CartierFiber.BundleCycles.principalCartierFiberCycleMap_push j a f hzero d) z
  exact (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget j f d _).symm.trans
    ((congrArg (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d) h).trans (Principal.CartierFiber.BundleCycles.principalCartierPointMap_graded a f d z).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecializationCycleForgetting.BundleCycles
