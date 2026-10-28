import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicRegularSpectrum
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.EndomorphismAction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSpectrumTransfer

/-! # Intrinsic Weil -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicWeil

noncomputable section

/-! The native degree-one Weil theorem for the constructed geometric
Frobenius operator, with the rational annihilator supplied by actual End⁰. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem geometric_h1_frobenius_absolute_values
    {k : Type u} [Field k] [Fintype k]
    (q : ℕ) (hq : Fintype.card k = q)
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0)
    (α : AlgebraicClosure ℚ_[ℓ]) (hα : (CohomologyPullback.Construction.geometricH1Frobenius ℓ k A).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧ ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = Real.sqrt (q : ℝ) := by
  have : FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) := Endomorphism.FiniteGeneration.Construction.rationalAlgebraicEnd_finiteDimensional A
  have he : ((Endomorphism.EndomorphismAction.Construction.rationalAlgebraicEndOppH1Action ℓ k A)
      (MulOpposite.op (Endomorphisms.Construction.rationalAlgebraicFrobenius k A))).HasEigenvalue α := by
    rwa [Endomorphism.EndomorphismAction.Construction.rationalAlgebraicEndOppH1Action_frobenius]
  have h := RegularSpectrumTransfer.Construction.algebraic_and_conjugates_of_regular_spectrum (Endomorphism.EndomorphismAction.Construction.rationalAlgebraicEndOppH1Action ℓ k A)
    (Endomorphisms.Construction.rationalAlgebraicFrobenius k A) (Fintype.card k : ℝ)
    (IntrinsicRegularSpectrum.Construction.frobeniusRationalRegular_complex_eigenvalue_norm k A) α he
  simpa only [hq] using h

theorem weil_frobenius_absolute_values
    {k : Type u} [Field k] [Fintype k]
    (q : ℕ) (hq : Fintype.card k = q)
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {H : Type*} [AddCommGroup H] [Module (AlgebraicClosure ℚ_[ℓ]) H]
    (F : Module.End (AlgebraicClosure ℚ_[ℓ]) H) (hF : CohomologyPullback.IsEtaleH1GeometricFrobenius A ℓ F)
    (α : AlgebraicClosure ℚ_[ℓ]) (hα : F.HasEigenvalue α) :
    IsAlgebraic ℚ α ∧ ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = Real.sqrt (q : ℝ) :=
  geometric_h1_frobenius_absolute_values q hq A ℓ hℓ α (CohomologyPullback.Construction.realized_eigenvalue ℓ A F hF α hα)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicWeil
