import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.EssentialSmoothFlat

/-! # Flat Section Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatSectionCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual flat polynomial coordinates generating the local section ideal -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing B] [Nontrivial A]

theorem smoothSection_exists_flat_kernelCoordinates :
    ∃ (ι : Type) (_ : Finite ι) (v : ι → RingHom.ker (algebraMap B A)),
      Ideal.span (Set.range (fun i => (v i).val)) = RingHom.ker (algebraMap B A) ∧
        letI := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
        Algebra.FormallyEtale (MvPolynomial ι A) B ∧ Module.Flat (MvPolynomial ι A) B := by
  obtain ⟨ι, hι, v, hv, he⟩ := Smooth.SectionCoordinates.BundleCycles.smoothSection_exists_generating_etaleCoordinates A B
  let : Finite ι := hι
  let := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
  let := DifferentialCoordinates.BundleCycles.differentialCoordinate_scalarTower (R := A) (fun i => (v i).val)
  have : Algebra.FormallyEtale (MvPolynomial ι A) B := he
  have : Algebra.EssFiniteType (MvPolynomial ι A) B := Algebra.EssFiniteType.of_comp A _ _
  exact ⟨ι, hι, v, hv, he, EssentialSmoothFlat.BundleCycles.formallySmooth_flat_of_essFiniteType (MvPolynomial ι A) B⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatSectionCoordinates.BundleCycles
