import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AlgebraIdealCoefficients

/-! # Coefficient Containment -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientContainment

noncomputable section

/-! Linear coefficients of a projective module detect containment in
every extended base ideal. -/

universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Projective R M] {ι : Type w} (x : ι → M)

theorem projectiveCoefficient_le_iff_smul (J : Ideal R) :
    SectionCoefficientIdeal.projectiveSectionCoefficientIdeal x ≤ J ↔
      ∀ i, x i ∈ J • (⊤ : Submodule R M) := by
  rw [SectionCoefficientIdeal.projectiveSectionCoefficientIdeal, Ideal.span_le]
  constructor
  · intro h i
    obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
    rw [← hs (x i), Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro m hm
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    exact h ⟨(i, (Finsupp.lapply m).comp s), rfl⟩
  · intro h r hr
    obtain ⟨⟨i, l⟩, rfl⟩ := hr
    have hl : J • (⊤ : Submodule R M) ≤ Submodule.comap l (J : Submodule R R) := by
      apply Submodule.smul_le.mpr
      intro a ha m _
      change l (a • m) ∈ J
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right (l m) J ha
    exact hl (h i)

theorem projectiveAlgebraIdealCoefficients_containment
    (B : Type v) [CommRing B] [Algebra R B] [Module.Projective R B]
    (K : Ideal B) (J : Ideal R) :
    AlgebraIdealCoefficients.projectiveAlgebraIdealCoefficients R B K ≤ J ↔ K ≤ J.map (algebraMap R B) := by
  rw [AlgebraIdealCoefficients.projectiveAlgebraIdealCoefficients, projectiveCoefficient_le_iff_smul]
  simp only [Ideal.smul_top_eq_map]
  constructor
  · exact fun h b hb => h ⟨b, hb⟩
  · exact fun h b => h b.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientContainment
