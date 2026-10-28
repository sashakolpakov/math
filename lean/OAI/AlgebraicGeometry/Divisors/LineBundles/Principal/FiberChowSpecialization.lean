import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting

/-! # Fiber Chow Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberChowSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization from the punctured scheme descends to genuine Chow groups

Every relation on the open lifts to an actual ambient relation. Lift
independence and the proved principal Cartier descent kill its image.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (a : Γ(X, ⊤))
    (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def principalFiberClassSpecialization (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) →₀ ℚ) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d).comp (FiberSpecialization.BundleCycles.principalFiberCycleSpecialization i j a f d)

include hcomp hzero in
theorem principalFiberClassSpecialization_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) (d + 1) ≤
      LinearMap.ker (principalFiberClassSpecialization i j a f d) := by
  intro z hz
  obtain ⟨w, hw, hres⟩ := Submodule.mem_map.mp
    (Open.RelationLifting.BundleCycles.openDimensionCycleRestriction_relations_lift i f (d + 1) hz)
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d (FiberSpecialization.BundleCycles.principalFiberCycleSpecialization i j a f d z) = 0
  rw [FiberSpecialization.BundleCycles.principalFiberCycleSpecialization_of_lift i j hcomp a hzero f d z w hres]
  exact CartierChow.BundleCycles.principalCartierFiberClassMap_relations j a hzero f d hw

def principalFiberChowSpecialization (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) (d + 1)).liftQ
    (principalFiberClassSpecialization i j a f d)
    (principalFiberClassSpecialization_relations i j hcomp a hzero f d)

@[simp]
theorem principalFiberChowSpecialization_cycle (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) →₀ ℚ) :
    principalFiberChowSpecialization i j hcomp a hzero f d
      (DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) (d + 1) z) = principalFiberClassSpecialization i j a f d z := rfl

theorem principalFiberChowSpecialization_of_lift (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) →₀ ℚ)
    (w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ)
    (hw : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) w = z) :
    principalFiberChowSpecialization i j hcomp a hzero f d
      (DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) (d + 1) z) = CartierFiber.BundleCycles.principalCartierFiberClassMap j a f d w := by
  rw [principalFiberChowSpecialization_cycle]
  exact congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d)
    (FiberSpecialization.BundleCycles.principalFiberCycleSpecialization_of_lift i j hcomp a hzero f d z w hw)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberChowSpecialization.BundleCycles
