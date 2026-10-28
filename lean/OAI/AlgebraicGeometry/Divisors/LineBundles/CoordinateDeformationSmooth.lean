import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.EtaleBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialCoordinates

/-! # Coordinate Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinateDeformationSmooth.BundleCycles

noncomputable section

/-! Deformation in actual flat formally étale coordinates is formally
smooth over the original coefficient ring. -/

variable {A B ι : Type} [CommRing A] [CommRing B] [Algebra A B] [Finite ι]

omit [Finite ι] in
theorem coordinateIdeal_map (v : ι → B) :
    (MvPolynomial.idealOfVars ι A).map (MvPolynomial.aeval v).toRingHom = Ideal.span (Set.range v) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range (funext fun i => MvPolynomial.aeval_X v i))

theorem coordinateDeformation_formallySmooth (v : ι → B) :
    letI := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) v
    Algebra.FormallyEtale (MvPolynomial ι A) B → Module.Flat (MvPolynomial ι A) B →
      Algebra.FormallySmooth A (Deformation.Iff.BundleCycles.deformationAlgebra (Ideal.span (Set.range v))) := by
  let := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) v
  let := DifferentialCoordinates.BundleCycles.differentialCoordinate_scalarTower (R := A) v
  intro he hf
  let I := MvPolynomial.idealOfVars ι A
  let J := I.map (algebraMap (MvPolynomial ι A) B)
  let D := Deformation.Iff.BundleCycles.deformationAlgebra I
  let E := Deformation.Iff.BundleCycles.deformationAlgebra J
  let := (Deformation.Maps.BundleCycles.deformationMap I J (algebraMap (MvPolynomial ι A) B) Ideal.le_comap_map).toAlgebra
  let : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A E a = Deformation.Maps.BundleCycles.deformationMap I J (algebraMap (MvPolynomial ι A) B) Ideal.le_comap_map
      (algebraMap A D a)
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial ι A) D, Deformation.Maps.BundleCycles.deformationMap_algebraMap,
      ← IsScalarTower.algebraMap_apply A (MvPolynomial ι A) B,
      ← IsScalarTower.algebraMap_apply A B E])
  let : Algebra.Smooth A D := Polynomial.DeformationSmooth.BundleCycles.polynomialDeformation_smooth A ι
  let : Algebra.FormallyEtale D E := Deformation.EtaleBaseChange.BundleCycles.deformationMap_formallyEtale I B
  have h : Algebra.FormallySmooth A E := Algebra.FormallySmooth.comp A D E
  have hJ : J = Ideal.span (Set.range v) := coordinateIdeal_map v
  exact hJ ▸ h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinateDeformationSmooth.BundleCycles
