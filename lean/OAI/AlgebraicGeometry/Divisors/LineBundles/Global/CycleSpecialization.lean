import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization
import OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint

/-! # Cycle Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: global specialization on finite rational cycles

Each point indexes its actual reduced integral closed subscheme. Its
specialization is the divisor of t on the constructed support deformation,
pushed into the global cone. Linear extension gives specialization of
finite rational cycles. Grading and rational-equivalence descent are
separate assertions and are not assumed here.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance specializationSupport_isIntegral (W : IrreducibleCloseds X) :
    IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).subscheme := CycleClass.Geometric.GenericPoint.reducedSupportScheme_isIntegral W

variable [AlgebraicGeometry.IsNoetherian X]

/-- The specialization cycle of an actual reduced integral closed support. -/
def globalIntegralSupportSpecialization (W : IrreducibleCloseds X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Support.Specialization.BundleCycles.globalClosedSupportSpecialization I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)

/-- The specialization cycle indexed by the generic point of its integral support. -/
def globalPrimeSpecialization (x : X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  globalIntegralSupportSpecialization I (irreducibleSetEquivPoints.symm x)

theorem globalPrimeSpecialization_genericPoint (W : IrreducibleCloseds X) :
    globalPrimeSpecialization I (irreducibleSetEquivPoints W) = globalIntegralSupportSpecialization I W := by
  unfold globalPrimeSpecialization
  exact congrArg (globalIntegralSupportSpecialization I) (irreducibleSetEquivPoints.symm_apply_apply W)

theorem globalPrimeSpecialization_nonnegative (x : X) (y : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalPrimeSpecialization I x y :=
  Support.Specialization.BundleCycles.globalClosedSupportSpecialization_nonnegative I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) y

/-- Rational coefficients on the same finite geometric specialization cycle. -/
def globalPrimeSpecializationQ (x : X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℚ :=
  (globalPrimeSpecialization I x).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

/-- Global specialization of finite rational cycles, before passage to Chow groups. -/
def globalCycleSpecialization : (X →₀ ℚ) →ₗ[ℚ] (SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℚ) :=
  Finsupp.linearCombination ℚ (globalPrimeSpecializationQ I)

@[simp]
theorem globalCycleSpecialization_single (x : X) (q : ℚ) :
    globalCycleSpecialization I (Finsupp.single x q) = q • globalPrimeSpecializationQ I x :=
  Finsupp.linearCombination_single ℚ q x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization.BundleCycles
