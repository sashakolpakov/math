import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRegular
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Jacobson.Ring

/-! # Cotangent Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension.Construction

noncomputable section

/-! Cotangent spaces and ranks of differentials in the Openness dimension argument. -/

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

/-- At a point with formally etale residue field, the cotangent space of a
formally smooth algebra is the residue fiber of its differentials. -/
def cotangentSpaceEquivTensorKaehler
    (K B : Type*) [CommRing K] [CommRing B] [Algebra K B] [IsLocalRing B]
    [Algebra.FormallySmooth K B] [Algebra.FormallyEtale K (ResidueField B)] :
    CotangentSpace B ≃ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄K] := by
  have hsurj : Function.Surjective (algebraMap B (ResidueField B)) := residue_surjective
  have hinj : Function.Injective (kerCotangentToTensor K B (ResidueField B)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj).mpr inferInstance
  have honto : Function.Surjective (kerCotangentToTensor K B (ResidueField B)) := by
    rw [← LinearMap.range_eq_top, range_kerCotangentToTensor K B (ResidueField B) hsurj]
    rw [Subsingleton.elim (mapBaseChange K B (ResidueField B)) 0, LinearMap.ker_zero]
    rfl
  let e : CotangentSpace B ≃ₗ[B] ResidueField B ⊗[B] Ω[B⁄K] :=
    Ideal.Cotangent.equivOfEq _ _ (by rw [ResidueField.algebraMap_eq, ker_residue]) ≪≫ₗ
      LinearEquiv.ofBijective (kerCotangentToTensor K B (ResidueField B)) ⟨hinj, honto⟩
  exact e.extendScalarsOfSurjective hsurj

/-- A regular local smooth algebra with etale residue field has dimension
equal to the rank of the fiber of its differentials. -/
theorem ringKrullDim_eq_finrank_tensorKaehler
    (K B : Type*) [CommRing K] [CommRing B] [Algebra K B]
    [IsRegularLocalRing B] [Algebra.FormallySmooth K B]
    [Algebra.FormallyEtale K (ResidueField B)] :
    ringKrullDim B = (Module.finrank (ResidueField B)
      (ResidueField B ⊗[B] Ω[B⁄K]) : WithBot ℕ∞) := by
  rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace B).mp inferInstance,
    (cotangentSpaceEquivTensorKaehler K B).finrank_eq]

/-- At a prime with etale residue field, a smooth algebra over a regular
ring has local dimension equal to the rank of its differentials. -/
theorem ringKrullDim_localization_eq_rankAtStalk_kaehler
    (K B : Type*) [CommRing K] [CommRing B] [Algebra K B]
    [IsRegularRing K] [Algebra.Smooth K B]
    (p : Ideal B) [hp : p.IsPrime]
    [Algebra.FormallyEtale K (ResidueField (Localization.AtPrime p))] :
    ringKrullDim (Localization.AtPrime p) =
      (Module.rankAtStalk Ω[B⁄K] ⟨p, hp⟩ : WithBot ℕ∞) := by
  have : IsRegularRing B := SmoothRegular.Construction.isRegularRing_of_smooth K B
  let Bp := Localization.AtPrime p
  have : Module.Free Bp Ω[Bp⁄K] := Module.free_of_flat_of_isLocalRing
  rw [ringKrullDim_eq_finrank_tensorKaehler K Bp, Module.finrank_baseChange]
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  exact congrArg (fun n : ℕ => (n : WithBot ℕ∞))
    (tensorKaehlerEquivOfFormallyEtale K B Bp).finrank_eq.symm

/-- Over a perfect field this dimension formula applies at every closed point. -/
theorem ringKrullDim_localization_maximal_eq_rankAtStalk_kaehler
    (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Algebra.Smooth K B] (p : Ideal B) [hp : p.IsMaximal] :
    ringKrullDim (Localization.AtPrime p) =
      (Module.rankAtStalk Ω[B⁄K] ⟨p, hp.isPrime⟩ : WithBot ℕ∞) := by
  have : Algebra.FiniteType K p.ResidueField :=
    (inferInstance : Algebra.FiniteType K B).trans
      (inferInstance : Algebra.FiniteType B p.ResidueField)
  have : Module.Finite K p.ResidueField :=
    finite_of_finite_type_of_isJacobsonRing K p.ResidueField
  have : Algebra.FormallyEtale K p.ResidueField :=
    Algebra.FormallyEtale.of_isSeparable K p.ResidueField
  exact ringKrullDim_localization_eq_rankAtStalk_kaehler K B p

/-- Differential rank in a smooth family is locally constant. -/
theorem isLocallyConstant_rankAtStalk_kaehler
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B] :
    IsLocallyConstant (Module.rankAtStalk (R := B) Ω[B⁄R]) :=
  Module.isLocallyConstant_rankAtStalk

/-- Formation of differential rank commutes with arbitrary base change. -/
theorem rankAtStalk_kaehler_baseChange
    (R S B C : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R B C]
    [Algebra.IsPushout R S B C] [Algebra.Smooth R B] (p : PrimeSpectrum C) :
    Module.rankAtStalk Ω[C⁄S] p =
      Module.rankAtStalk Ω[B⁄R] (p.comap (algebraMap B C)) := by
  rw [← Module.rankAtStalk_eq_of_equiv (tensorKaehlerEquiv R S B C)]
  exact Module.rankAtStalk_baseChange p

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension.Construction
