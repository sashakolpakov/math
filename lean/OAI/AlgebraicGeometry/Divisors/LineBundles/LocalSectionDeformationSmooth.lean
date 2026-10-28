import OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinateDeformationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatSectionCoordinates

/-! # Local Section Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalSectionDeformationSmooth.BundleCycles

noncomputable section

/-! The deformation of a genuine local smooth ring section is formally
smooth, using its constructed flat étale kernel coordinates. -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing B] [Nontrivial A]

theorem localSection_deformation_formallySmooth :
    Algebra.FormallySmooth A (Deformation.Iff.BundleCycles.deformationAlgebra (RingHom.ker (algebraMap B A))) := by
  obtain ⟨ι, hι, v, hv, he, hf⟩ := FlatSectionCoordinates.BundleCycles.smoothSection_exists_flat_kernelCoordinates A B
  let := hι
  have h := CoordinateDeformationSmooth.BundleCycles.coordinateDeformation_formallySmooth (A := A) (fun i => (v i).val) he hf
  exact hv ▸ h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalSectionDeformationSmooth.BundleCycles
