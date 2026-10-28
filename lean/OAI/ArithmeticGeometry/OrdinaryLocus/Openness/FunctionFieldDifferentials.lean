import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CotangentDimension
import Mathlib.RingTheory.Localization.FractionRing

/-! # Function Field Differentials -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FunctionFieldDifferentials.Construction

noncomputable section

/-! Differential dimension of function fields of smooth integral affine schemes. -/

open KaehlerDifferential
open scoped TensorProduct

/-- The rank of differentials at any prime of a smooth integral algebra
equals the differential dimension of its fraction field. -/
theorem finrank_fractionField_kaehler_eq_rankAtStalk
    (K B Q : Type*) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] [Field Q] [Algebra B Q] [IsFractionRing B Q]
    [Algebra K Q] [IsScalarTower K B Q] (p : PrimeSpectrum B) :
    Module.finrank Q Ω[Q⁄K] = Module.rankAtStalk Ω[B⁄K] p := by
  have : Algebra.FormallyEtale B Q :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Q) (nonZeroDivisors B)
  let q : PrimeSpectrum Q := ⟨⊥, inferInstance⟩
  have hq : q.comap (algebraMap B Q) = ⊥ := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap B Q)).mp (IsFractionRing.injective B Q)
  have h := Module.rankAtStalk_isBaseChange
    (isBaseChange_of_formallyEtale K B Q) q
  rw [Module.rankAtStalk_eq_finrank_of_free, hq] at h
  exact h.trans (Module.rankAtStalk_eq_of_le_of_finite_of_flat Ω[B⁄K] bot_le)

/-- At a closed point of a smooth integral algebra over a perfect field,
the local dimension equals the differential dimension of the function field. -/
theorem finrank_fractionField_kaehler_eq_local_dimension
    (K B Q : Type*) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] [Field Q] [Algebra B Q] [IsFractionRing B Q]
    [Algebra K Q] [IsScalarTower K B Q] (p : Ideal B) [hp : p.IsMaximal] :
    (Module.finrank Q Ω[Q⁄K] : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p) := by
  rw [finrank_fractionField_kaehler_eq_rankAtStalk K B Q ⟨p, hp.isPrime⟩]
  exact (CotangentDimension.Construction.ringKrullDim_localization_maximal_eq_rankAtStalk_kaehler K B p).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FunctionFieldDifferentials.Construction
