import OAI.AlgebraicGeometry.Divisors.LineBundles.InfinitesimalCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialCoordinates
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Coordinate Power Contraction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinatePowerContraction.BundleCycles

noncomputable section

/-! # LineBundleCycles: every power of the actual coordinate ideal has the expected contraction -/

variable {A B ι : Type} [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A]

theorem variableIdeal_eq_constantCoeff_ker :
    MvPolynomial.idealOfVars ι A = RingHom.ker MvPolynomial.constantCoeff := by
  ext p
  rw [← pow_one (MvPolynomial.idealOfVars ι A), MvPolynomial.mem_pow_idealOfVars_iff',
    RingHom.mem_ker]
  change (∀ d, d.degree < 1 → p.coeff d = 0) ↔ p.coeff 0 = 0
  constructor
  · exact fun h => h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simpa only [hd0] using h

theorem coordinateSection_comp (v : ι → RingHom.ker (algebraMap B A)) :
    (algebraMap B A).comp (MvPolynomial.aeval (R := A) (fun i => (v i).val)).toRingHom =
      MvPolynomial.constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change algebraMap B A (MvPolynomial.aeval (R := A) (fun j => (v j).val) (MvPolynomial.C a)) = _
    rw [MvPolynomial.aeval_C]
    rw [← IsScalarTower.algebraMap_apply A B A, MvPolynomial.constantCoeff_C]
    rfl
  · intro i
    change algebraMap B A (MvPolynomial.aeval (R := A) (fun j => (v j).val) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X, MvPolynomial.constantCoeff_X]
    exact (v i).property

theorem coordinateSection_power_comap (v : ι → RingHom.ker (algebraMap B A))
    (n : ℕ) :
    letI := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
    Algebra.FormallySmooth (MvPolynomial ι A) B →
      (RingHom.ker (algebraMap B A) ^ n).comap (algebraMap (MvPolynomial ι A) B) =
        MvPolynomial.idealOfVars ι A ^ n := by
  let := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
  intro hs
  let : Algebra (MvPolynomial ι A) A := MvPolynomial.constantCoeff.toAlgebra
  let q : B →ₐ[MvPolynomial ι A] A := {
    toRingHom := algebraMap B A
    commutes' := fun p => DFunLike.congr_fun (coordinateSection_comp v) p
  }
  have hA : Function.Surjective (algebraMap (MvPolynomial ι A) A) :=
    fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C ι a⟩
  have h := InfinitesimalCoordinates.BundleCycles.formallySmooth_ker_power_comap_of_surjective q hA n
  change (RingHom.ker (algebraMap B A) ^ n).comap (algebraMap (MvPolynomial ι A) B) =
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial ι A →+* A) ^ n at h
  rw [← variableIdeal_eq_constantCoeff_ker] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CoordinatePowerContraction.BundleCycles
