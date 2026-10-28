import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport
import Mathlib.RingTheory.Localization.Ideal

/-! # Closure -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure.BundleCycles

noncomputable section

/-!
# LineBundleCycles: saturation of a deformed closed support

The coefficientwise support ideal is saturated with respect to t. Thus
localizing its defining ideal at t and contracting it recovers exactly
the same closed deformation, without adding components on the special fiber.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R]

theorem closedSupportDeformationRingMap_parameter (I P : Ideal R) :
    ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P (Iff.BundleCycles.deformationParameter I) =
      Iff.BundleCycles.deformationParameter (I.map (Ideal.Quotient.mk P)) :=
  Maps.BundleCycles.deformationMap_parameter I _ (Ideal.Quotient.mk P) _

/-- Multiplication by any power of t does not change membership in the
actual defining ideal of the deformed closed support. -/
theorem closedSupportDeformationKernel_saturated (I P : Ideal R)
    (p : Iff.BundleCycles.deformationAlgebra I) (n : ℕ) :
    Iff.BundleCycles.deformationParameter I ^ n * p ∈ RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) ↔
      p ∈ RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) := by
  simp only [RingHom.mem_ker, map_mul, map_pow, closedSupportDeformationRingMap_parameter]
  constructor
  · exact mem_nonZeroDivisors_iff_left.mp
      (pow_mem (Iff.BundleCycles.deformationParameter_regular (I.map (Ideal.Quotient.mk P))) n) _
  · intro h
    rw [h, mul_zero]

/-- Contracting the defining ideal from the punctured deformation gives
exactly the original ideal: this is the affine schematic-closure condition. -/
theorem closedSupportDeformationKernel_localize_contract (I P : Ideal R) :
    ((RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P)).map
      (algebraMap (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R))).comap
        (algebraMap (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R)) =
      RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) := by
  ext p
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers (Iff.BundleCycles.deformationParameter I))]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (closedSupportDeformationKernel_saturated I P p n).mp hm
  · intro hp
    exact ⟨1, Submonoid.one_mem _, by simpa only [one_mul] using hp⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure.BundleCycles
