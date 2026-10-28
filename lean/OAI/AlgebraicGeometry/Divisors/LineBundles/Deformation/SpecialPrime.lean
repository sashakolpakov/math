import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff

/-! # Special Prime -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SpecialPrime.BundleCycles

noncomputable section

/-! A prime on the actual special fiber lies over the center ideal. -/

variable {R : Type} [CommRing R] (I : Ideal R)

theorem deformationParameter_mul_negativeGenerator (r : R) (hr : r ∈ I) :
    Iff.BundleCycles.deformationParameter I * Iff.BundleCycles.deformationMonomial I (-1) r (by simpa using hr) =
      algebraMap R (Iff.BundleCycles.deformationAlgebra I) r := by
  apply Subtype.ext
  change AddMonoidAlgebra.single 1 1 * AddMonoidAlgebra.single (-1) r =
    AddMonoidAlgebra.single 0 r
  rw [AddMonoidAlgebra.single_mul_single, one_mul]
  rfl

theorem deformationSpecialPrime_liesOver_center
    (q : PrimeSpectrum (Iff.BundleCycles.deformationAlgebra I)) (hq : Iff.BundleCycles.deformationParameter I ∈ q.asIdeal) :
    I ≤ q.asIdeal.comap (algebraMap R (Iff.BundleCycles.deformationAlgebra I)) := by
  intro r hr
  change algebraMap R (Iff.BundleCycles.deformationAlgebra I) r ∈ q.asIdeal
  rw [← deformationParameter_mul_negativeGenerator I r hr]
  exact q.asIdeal.mul_mem_right _ hq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SpecialPrime.BundleCycles
