import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinatePowerContraction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeInjection

/-! # Coordinate Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.CoordinateCone.BundleCycles

noncomputable section

/-! # LineBundleCycles: the polynomial coordinates inject into the actual section normal cone -/

variable {A B ι : Type} [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]

theorem coordinateIdeal_le_comap (v : ι → RingHom.ker (algebraMap B A)) :
    MvPolynomial.idealOfVars ι A ≤ (RingHom.ker (algebraMap B A)).comap
      (MvPolynomial.aeval (R := A) (fun i => (v i).val)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change algebraMap B A (MvPolynomial.aeval (R := A) (fun j => (v j).val) (MvPolynomial.X i)) = 0
  rw [MvPolynomial.aeval_X]
  exact (v i).property

def sectionCoordinateConeMap (v : ι → RingHom.ker (algebraMap B A)) :
    MvPolynomial ι A →+* Normal.Cone.BundleCycles.NormalConeRing (RingHom.ker (algebraMap B A)) :=
  (Deformation.Maps.BundleCycles.normalConeMap (MvPolynomial.idealOfVars ι A) (RingHom.ker (algebraMap B A))
    (MvPolynomial.aeval (R := A) (fun i => (v i).val)).toRingHom (coordinateIdeal_le_comap v)).comp
      LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap

theorem sectionCoordinateConeMap_injective [IsScalarTower A B A]
    (v : ι → RingHom.ker (algebraMap B A)) :
    letI := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
    Algebra.FormallySmooth (MvPolynomial ι A) B → Function.Injective (sectionCoordinateConeMap v) := by
  let := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
  intro hs
  exact (Normal.ConeInjection.BundleCycles.normalConeMap_injective_of_power_comap _ _ _ (coordinateIdeal_le_comap v)
    (fun n => CoordinatePowerContraction.BundleCycles.coordinateSection_power_comap v n hs)).comp LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap_injective

theorem sectionCoordinateConeMap_C (v : ι → RingHom.ker (algebraMap B A)) (a : A) :
    sectionCoordinateConeMap v (MvPolynomial.C a) =
      Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal (RingHom.ker (algebraMap B A)))
        (algebraMap B (reesAlgebra (RingHom.ker (algebraMap B A))) (algebraMap A B a)) := by
  change Deformation.Maps.BundleCycles.normalConeMap _ _ _ _ (LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap (MvPolynomial.C a)) = _
  rw [LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap_C]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  change Polynomial.map _ (Polynomial.C (MvPolynomial.C a)) = Polynomial.C (algebraMap A B a)
  rw [Polynomial.map_C]
  exact congrArg Polynomial.C (MvPolynomial.aeval_C (R := A) (fun i => (v i).val) a)

theorem sectionCoordinateConeMap_X (v : ι → RingHom.ker (algebraMap B A)) (i : ι) :
    sectionCoordinateConeMap v (MvPolynomial.X i) =
      Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal (RingHom.ker (algebraMap B A)))
        (Normal.ConeSymmetric.BundleCycles.reesDegreeOne (RingHom.ker (algebraMap B A)) (v i)) := by
  change Deformation.Maps.BundleCycles.normalConeMap _ _ _ _ (LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap (MvPolynomial.X i)) = _
  rw [LineBundles.Polynomial.CoordinateCone.BundleCycles.polynomialCoordinateConeMap_X]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  change Polynomial.map _ (Polynomial.monomial 1 (MvPolynomial.X i)) = Polynomial.monomial 1 (v i).val
  rw [Polynomial.map_monomial]
  exact congrArg (Polynomial.monomial 1) (MvPolynomial.aeval_X (R := A) (fun j => (v j).val) i)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.CoordinateCone.BundleCycles
