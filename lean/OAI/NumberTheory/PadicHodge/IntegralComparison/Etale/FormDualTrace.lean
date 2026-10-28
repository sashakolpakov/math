import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.LineTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceModules

/-! # Form Dual Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualTrace

noncomputable section

/-! The original differential forms of a finite étale source are the
coefficient dual of target forms. The actual de Rham trace is evaluation
at the coefficient unit, in every degree. -/

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

def equiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n ≃ₗ[A]
    (B →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  ((FormScalarExtension.isBaseChange R A B σ n).equiv.symm.restrictScalars A).trans
    (FiniteEtale.LineTrace.equiv A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n))

omit [Fintype σ] in
theorem equiv_smul_map (n : ℕ) (b x : B) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    FormDualTrace.equiv R A B σ n (b • OrdinaryFormScalars.Ordinary.map R A B n ω) x =
      Algebra.trace A B (b * x) • ω := by
  change FiniteEtale.LineTrace.equiv A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)
    ((FormScalarExtension.isBaseChange R A B σ n).equiv.symm
      ((FormScalarExtension.isBaseChange R A B σ n).equiv (b ⊗ₜ[A] ω))) x = _
  rw [LinearEquiv.symm_apply_apply, FiniteEtale.LineTrace.equiv_tmul]

variable {ι : Type v} [Fintype ι] (b : Module.Basis ι A B)

theorem trace_eq_eval_one (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) :
    DeRhamTraceCoordinates.formTrace R A B σ b n ω = FormDualTrace.equiv R A B σ n ω 1 := by
  obtain ⟨z, rfl⟩ := (FormScalarExtension.isBaseChange R A B σ n).equiv.surjective ω
  induction z using TensorProduct.inductionOn with
  | tmul x η =>
      change DeRhamTraceCoordinates.formTrace R A B σ b n
        (x • OrdinaryFormScalars.Ordinary.map R A B n η) =
        FormDualTrace.equiv R A B σ n (x • OrdinaryFormScalars.Ordinary.map R A B n η) 1
      rw [DeRhamTraceCoordinates.trace_projection_formula, equiv_smul_map, mul_one]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem trace_symm (n : ℕ) (φ : B →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    DeRhamTraceCoordinates.formTrace R A B σ b n ((FormDualTrace.equiv R A B σ n).symm φ) = φ 1 := by
  rw [trace_eq_eval_one, LinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualTrace
