import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower

/-! # Cycle Power -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CyclePower.Cycles

noncomputable section

/-! Iterated line-bundle intersections on actual cycles, with
their dimension-graded quotient formula and support control. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def lineBundlePointPower : ℕ → ((X →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ))
  | 0 => LinearMap.id
  | n + 1 => (lineBundlePointPower n).comp (Intersection.Cycles.lineBundlePointIntersection L)

def lineBundleCyclePower (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    (n : ℕ) → ((Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + n) →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ))
  | 0 => LinearMap.id
  | n + 1 => (lineBundleCyclePower f d n).comp (Intersection.Cycles.lineBundleCycleIntersection L f (d + n))

theorem lineBundleCyclePower_forget (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d n : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + n) →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Cycles.lineBundleCyclePower L f d n z) =
      Cycles.lineBundlePointPower L n (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + n) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d
      (Cycles.lineBundleCyclePower L f d n (Intersection.Cycles.lineBundleCycleIntersection L f (d + n) z)) =
        Cycles.lineBundlePointPower L n (Intersection.Cycles.lineBundlePointIntersection L (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + (n + 1)) z))
    rw [ih]
    exact congrArg (Cycles.lineBundlePointPower L n) (Intersection.Cycles.lineBundlePointIntersection_graded L f (d + n) z).symm

theorem lineBundlePointPower_image_dimension_bound
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] (p : X ⟶ Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d n : ℕ) (z : X →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f ≤ d) :
    ∀ y, Cycles.lineBundlePointPower L n z y ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p y)) f ≤ d := by
  induction n generalizing z with
  | zero => exact hz
  | succ n ih =>
    exact ih (Intersection.Cycles.lineBundlePointIntersection L z)
      (IntersectionSupport.Cycles.lineBundlePointIntersection_image_dimension_bound L p f d z hz)

theorem separatedLineBundleChowPower_cycle [X.IsSeparated]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d n : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + n) →₀ ℚ) :
    SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + n) z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Cycles.lineBundleCyclePower L f d n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n)
      (SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle L f (d + n) z)).trans (ih _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CyclePower.Cycles
