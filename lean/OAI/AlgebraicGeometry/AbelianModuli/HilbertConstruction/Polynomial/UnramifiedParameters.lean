import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.PolynomialParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleLocalRegularSequences

/-! # Unramified Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.UnramifiedParameters

noncomputable section

/-! A flat unramified local algebra over polynomial coordinates has an actual regular generating sequence at every point lying over a rational coordinate point. The source localization and its local algebra map are constructed in the proof. -/
universe u v w
open IsLocalRing

theorem polynomial_unramified_flat_local_regular_parameters
    {K : Type u} [Field K] {ι : Type v} [Finite ι] (a : ι → K)
    (B : Type w) [CommRing B] [IsLocalRing B]
    [Algebra (MvPolynomial ι K) B]
    [Algebra.EssFiniteType (MvPolynomial ι K) B]
    [Algebra.FormallyUnramified (MvPolynomial ι K) B]
    [Module.Flat (MvPolynomial ι K) B]
    (hpoint : (maximalIdeal B).under (MvPolynomial ι K) =
      RingHom.ker (MvPolynomial.eval a)) :
    ∃ rs : List B, Regular.SequenceBasic.RingTheory.Sequence.IsRegular B rs ∧ Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal B ∧
      rs.length = Nat.card ι := by
  let A := MvPolynomial ι K
  let p : Ideal A := RingHom.ker (MvPolynomial.eval a)
  let : p.IsMaximal := EvaluationIdeal.polynomial_evaluation_kernel_isMaximal a
  let Aₚ := Localization.AtPrime p
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap A B y) := by
    intro y
    apply not_not.mp
    intro hn
    apply y.2
    change (y : A) ∈ RingHom.ker (MvPolynomial.eval a)
    rw [← hpoint]
    exact hn
  let ψ : Aₚ →+* B := IsLocalization.lift (S := Aₚ) hu
  let : Algebra Aₚ B := ψ.toAlgebra
  let : IsScalarTower A Aₚ B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hu).symm
  have hlocal : IsLocalHom ψ := by
    apply ((IsLocalRing.local_hom_TFAE ψ).out 3 1).mp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Aₚ, Ideal.map_map]
    change p.map (ψ.comp (algebraMap A Aₚ)) ≤ maximalIdeal B
    rw [show ψ.comp (algebraMap A Aₚ) = algebraMap A B from
      IsLocalization.lift_comp hu]
    exact Ideal.map_le_iff_le_comap.mpr hpoint.symm.le
  let : IsLocalHom (algebraMap Aₚ B) := hlocal
  let : Algebra.EssFiniteType Aₚ B := Algebra.EssFiniteType.of_comp A Aₚ B
  let : Algebra.FormallyUnramified Aₚ B :=
    Algebra.FormallyUnramified.of_restrictScalars A Aₚ B
  let : Module.Flat Aₚ B :=
    (Module.flat_iff_of_isLocalization Aₚ p.primeCompl B).mpr inferInstance
  obtain ⟨rs, hreg, hgen, hlen⟩ := Localized.PolynomialParameters.localized_polynomial_regular_parameters a Aₚ
  obtain ⟨hregB, hgenB⟩ :=
    EtaleLocalRegularSequences.local_unramified_flat_regular_generators Aₚ B rs hreg hgen
  exact ⟨rs.map (algebraMap Aₚ B), hregB, hgenB, by simpa only [List.length_map] using hlen⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.UnramifiedParameters
