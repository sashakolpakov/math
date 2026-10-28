import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualTrace

/-! # Form Dual Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualEvaluation

noncomputable section

/-! Coefficient evaluation in finite étale form duality is the actual
trace of the coefficient times the form. -/

open scoped TensorProduct

universe u v
variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Fintype σ] [LinearOrder σ]
  [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B]

omit [Fintype σ] in
theorem smul (n : ℕ) (b x : B) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :
    FormDualTrace.equiv R A B σ n (b • ω) x =
      FormDualTrace.equiv R A B σ n ω (b * x) := by
  obtain ⟨z, rfl⟩ := (FormScalarExtension.isBaseChange R A B σ n).equiv.surjective ω
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, smul_add, LinearMap.add_apply, hz, hw]
  | tmul y η =>
    change FormDualTrace.equiv R A B σ n
      (b • (y • OrdinaryFormScalars.Ordinary.map R A B n η)) x =
        FormDualTrace.equiv R A B σ n
          (y • OrdinaryFormScalars.Ordinary.map R A B n η) (b * x)
    rw [smul_smul, FormDualTrace.equiv_smul_map,
      FormDualTrace.equiv_smul_map]
    congr 2
    ring

variable {ι : Type v} [Fintype ι] (e : Module.Basis ι A B)

theorem trace_mul (n : ℕ) (b : B) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :
    DeRhamTraceCoordinates.formTrace R A B σ e n (b • ω) =
      FormDualTrace.equiv R A B σ n ω b := by
  rw [FormDualTrace.trace_eq_eval_one, smul, mul_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualEvaluation
