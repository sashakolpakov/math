import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientFrame

/-! # Monomial Chart Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialChartFractions

noncomputable section

/-! Equal-block-degree monomials admit a fraction in the actual chart
ring whenever the denominator divides a power of the balanced denominator. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem chartFraction_crossMultiply_power
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) (g : ℕ → Submodule R S) [GradedAlgebra g]
    (f : S) {d : ℕ} (hf : f ∈ g d) (k : ℕ) (x : S) (hx : x ∈ g (k • d))
    (b c : A) (h : x.val * b = f.val ^ k * c) :
    Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f (HomogeneousLocalization.Away.mk g hf k x hx) *
      algebraMap A (Localization.Away f.val) b = algebraMap A (Localization.Away f.val) c := by
  rw [Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_mk, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
    mul_comm b, h]
  exact IsLocalization.mk'_mul_cancel_left c (⟨f.val ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f.val)

variable (R : Type u) [CommRing R] {r m : ℕ}

def balancedMonomialChartFraction (i : Fin m) (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (k : ℕ)
    (b d C : (Fin r → Fin m) → ℕ) (he : C + b = k • a)
    (hd : ∀ j, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight d j = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b j) :
    FrameChartCoordinates.balancedDeterminantChartRing R i a ha := by
  have hka : k • a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight :=
    (ExponentFiniteGeneration.balancedExponentMonoid _).nsmul_mem ha k
  have hQ : C + d ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight :=
    ExponentCompletion.balanced_completion_of_same_degree _ _ _ _ _ hka he hd
  have hdeg : ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (C + d) i =
      k • ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i := by
    rw [ExponentFiniteGeneration.monomialMultiDegree_add, hd, ← ExponentFiniteGeneration.monomialMultiDegree_add, he, ExponentCompletion.monomialMultiDegree_nsmul, nsmul_eq_mul, Nat.cast_id]
  exact HomogeneousLocalization.Away.mk (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i) k
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (C + d) hQ)
    (hdeg ▸ FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R (C + d) hQ i)

theorem balancedMonomialChartFraction_crossMultiply (i : Fin m) (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (k : ℕ)
    (b d C : (Fin r → Fin m) → ℕ) (he : C + b = k • a)
    (hd : ∀ j, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight d j = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b j) :
    (show BalancedChart.AmbientFrame.balancedChartAmbientRing R a from
      Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
        (DeterminantGrading.balancedDeterminantGrading R r m i) (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
        (balancedMonomialChartFraction R i a ha k b d C he hd)) *
        MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (BalancedChart.AmbientFrame.balancedChartAmbientVectors R a)) b =
      MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (BalancedChart.AmbientFrame.balancedChartAmbientVectors R a)) d := by
  rw [BalancedChart.AmbientFrame.balancedChartAmbientVectors_monomial, BalancedChart.AmbientFrame.balancedChartAmbientVectors_monomial]
  have hpoly : MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) b *
      MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (C + d) =
        (MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a) ^ k *
          MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) d := by
    rw [MonomialAlgebra.exponentMonomial_add]
    calc
      _ = MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (C + b) *
          MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) d := by rw [MonomialAlgebra.exponentMonomial_add]; ring
      _ = _ := by rw [he, NonvanishingMonomialCompletion.exponentMonomial_nsmul]
  unfold balancedMonomialChartFraction
  apply chartFraction_crossMultiply_power
  exact (mul_comm _ _).trans hpoly

theorem supportedMonomial_exists_chart_fraction (i : Fin m) (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (b d : (Fin r → Fin m) → ℕ)
    (hsupp : ∀ τ, b τ ≠ 0 → 0 < a τ)
    (hd : ∀ j, ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight d j = ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight b j) :
    ∃ F : FrameChartCoordinates.balancedDeterminantChartRing R i a ha,
      (show BalancedChart.AmbientFrame.balancedChartAmbientRing R a from
        Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
          (DeterminantGrading.balancedDeterminantGrading R r m i) (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha) F) *
          MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (BalancedChart.AmbientFrame.balancedChartAmbientVectors R a)) b =
        MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (BalancedChart.AmbientFrame.balancedChartAmbientVectors R a)) d := by
  obtain ⟨k, _, C, hC⟩ := SupportedExponentCompletion.supportedExponent_exists_completion a b hsupp
  exact ⟨balancedMonomialChartFraction R i a ha k b d C hC hd,
    balancedMonomialChartFraction_crossMultiply R i a ha k b d C hC hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialChartFractions
