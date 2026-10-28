import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierSelfIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization

/-! # Fiber Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization of cycles from the punctured parameter locus

Close the generic-point supports of a cycle on the open and intersect
with the global parameter. Any two cycle lifts differ by a cycle on the
closed zero fiber, whose principal self-intersection is proved zero.
This yields an actual lift-independent specialization on finite cycles.
Descent of principal relations is still a separate requirement.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X Z : Scheme} [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian X]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (a : Γ(X, ⊤))
    (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

include hcomp hzero in
/-- The principal fiber intersection is independent of every choice of ambient cycle lift. -/
theorem principalCartierFiberCycleMap_lift_independent (d : ℕ)
    (z w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ)
    (h : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) z = Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) w) :
    CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d z = CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d w := by
  have hz : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) (z - w) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨v, hv⟩ := CycleLocalization.BundleCycles.exists_closedDimensionCycle_of_zero_restriction i j hcomp f (d + 1) (z - w) hz
  have hcap := LinearMap.congr_fun (CartierSelfIntersection.BundleCycles.principalCartierFiberCycleMap_closed j a hzero f d) v
  change CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f (d + 1) v) = 0 at hcap
  rw [hv, map_sub] at hcap
  exact sub_eq_zero.mp hcap

/-- Specialization from finite cycles on the open, via their actual closures. -/
def principalFiberCycleSpecialization (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ) :=
  (CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d).comp (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension i f (d + 1))

include hcomp hzero in
/-- Any actual ambient lift computes the same specialization cycle. -/
theorem principalFiberCycleSpecialization_of_lift (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) →₀ ℚ)
    (w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ)
    (hw : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) w = z) :
    principalFiberCycleSpecialization i j a f d z = CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d w :=
  principalCartierFiberCycleMap_lift_independent i j hcomp a hzero f d _ w
    ((Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction_extension i f (d + 1) z).trans hw.symm)

include hcomp hzero in
theorem principalFiberCycleSpecialization_restriction (d : ℕ)
    (w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    principalFiberCycleSpecialization i j a f d (Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) w) =
      CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d w :=
  principalFiberCycleSpecialization_of_lift i j hcomp a hzero f d _ w rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSpecialization.BundleCycles
