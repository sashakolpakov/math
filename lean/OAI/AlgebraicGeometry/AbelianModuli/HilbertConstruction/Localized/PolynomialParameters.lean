import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EvaluationIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceFlatBaseChange

/-! # Polynomial Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.PolynomialParameters

noncomputable section

/-! Localizing the polynomial ring at a rational point produces a regular sequence of maximal-ideal generators of exactly the coordinate dimension. -/
universe u v w
open IsLocalRing

local instance evaluationKernelPrime {K : Type u} [Field K] {ι : Type v} (a : ι → K) :
    (RingHom.ker (MvPolynomial.eval a)).IsPrime := by
  let := Polynomial.EvaluationIdeal.polynomial_evaluation_kernel_isMaximal a
  infer_instance

theorem localized_polynomial_regular_parameters
    {K : Type u} [Field K] {ι : Type v} [Finite ι] (a : ι → K)
    (S : Type w) [CommRing S] [Algebra (MvPolynomial ι K) S]
    [IsLocalRing S] [IsLocalization.AtPrime S (RingHom.ker (MvPolynomial.eval a))] :
    ∃ rs : List S, Regular.SequenceBasic.RingTheory.Sequence.IsRegular S rs ∧ Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal S ∧
      rs.length = Nat.card ι := by
  let p : Ideal (MvPolynomial ι K) := RingHom.ker (MvPolynomial.eval a)
  let : p.IsMaximal := Polynomial.EvaluationIdeal.polynomial_evaluation_kernel_isMaximal a
  obtain ⟨rs, hreg, hgen, hlen⟩ := Polynomial.EvaluationIdeal.polynomial_evaluation_regular_generators a
  have hmem : ∀ r ∈ rs, r ∈ p := by
    intro r hr
    change r ∈ RingHom.ker (MvPolynomial.eval a)
    rw [← hgen]
    exact Ideal.subset_span hr
  refine ⟨rs.map (algebraMap (MvPolynomial ι K) S),
    Regular.SequenceFlatBaseChange.weaklyRegular_regular_localization S p hreg.1 hmem, ?_, ?_⟩
  · rw [← Regular.SequenceBasic.Ideal.map_ofList, hgen]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal p S
  · simpa only [List.length_map] using hlen

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.PolynomialParameters
