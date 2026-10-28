import OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtContinuity

/-! # Orthonormalization Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalizationContinuity.Construction

noncomputable section

/-! Normalized Gram--Schmidt vectors, and the resulting orthonormal
basis, vary continuously on independent families. -/

open InnerProductSpace

theorem gramSchmidtNormed_continuous_family
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f : X → Fin n → E) (hf : ∀ i, Continuous (fun x => f x i))
    (hli : ∀ x, LinearIndependent ℝ (f x)) (i : Fin n) :
    Continuous (fun x => gramSchmidtNormed ℝ (f x) i) := by
  have hc := GramSchmidtContinuity.Construction.gramSchmidt_continuous_family f hf hli i
  exact (hc.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hli x)))).smul hc

theorem gramSchmidtOrthonormalBasis_continuous_family
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (h : Module.finrank ℝ E = Fintype.card (Fin n))
    (f : X → Fin n → E) (hf : ∀ i, Continuous (fun x => f x i))
    (hli : ∀ x, LinearIndependent ℝ (f x)) (i : Fin n) :
    Continuous (fun x => gramSchmidtOrthonormalBasis h (f x) i) := by
  have he (x : X) : gramSchmidtOrthonormalBasis h (f x) i = gramSchmidtNormed ℝ (f x) i := by
    apply gramSchmidtOrthonormalBasis_apply
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i (hli x)]
    exact one_ne_zero
  simp_rw [he]
  exact gramSchmidtNormed_continuous_family f hf hli i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalizationContinuity.Construction
