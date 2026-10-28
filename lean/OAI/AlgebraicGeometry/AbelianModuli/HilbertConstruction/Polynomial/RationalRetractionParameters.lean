import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.UnramifiedParameters

/-! # Rational Retraction Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.RationalRetractionParameters

noncomputable section

/-! A retraction to the ground field determines the rational polynomial point needed for explicit regular parameters. The point condition is derived from the retraction, not supplied as a hypothesis. -/
universe u v w
open IsLocalRing

theorem polynomial_flat_unramified_retraction_regular_parameters
    {K : Type u} [Field K] {ι : Type v} [Finite ι]
    (B : Type w) [CommRing B] [IsLocalRing B]
    [Algebra (MvPolynomial ι K) B]
    [Algebra.EssFiniteType (MvPolynomial ι K) B]
    [Algebra.FormallyUnramified (MvPolynomial ι K) B]
    [Module.Flat (MvPolynomial ι K) B]
    (ε : B →+* K)
    (hsplit : (ε.comp (algebraMap (MvPolynomial ι K) B)).comp MvPolynomial.C =
      RingHom.id K) :
    ∃ rs : List B, Regular.SequenceBasic.RingTheory.Sequence.IsRegular B rs ∧ Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal B ∧
      rs.length = Nat.card ι := by
  let φ := algebraMap (MvPolynomial ι K) B
  let a : ι → K := fun i => ε (φ (MvPolynomial.X i))
  have hsurj : Function.Surjective ε := by
    intro k
    exact ⟨φ (MvPolynomial.C k), RingHom.congr_fun hsplit k⟩
  have hker : RingHom.ker ε = maximalIdeal B := IsLocalRing.ker_eq_maximalIdeal ε hsurj
  have heval : ε.comp φ = MvPolynomial.eval a := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simpa only [RingHom.comp_apply, MvPolynomial.eval_C, RingHom.id_apply] using
        RingHom.congr_fun hsplit k
    · intro i
      simp [a]
  apply UnramifiedParameters.polynomial_unramified_flat_local_regular_parameters a B
  ext f
  change φ f ∈ maximalIdeal B ↔ MvPolynomial.eval a f = 0
  rw [← hker]
  change ε (φ f) = 0 ↔ MvPolynomial.eval a f = 0
  rw [← RingHom.comp_apply, heval]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.RationalRetractionParameters
