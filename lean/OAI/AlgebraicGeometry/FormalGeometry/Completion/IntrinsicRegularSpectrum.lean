import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicFrobeniusPolynomialHeight
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialHeightSpectrum

/-! # Intrinsic Regular Spectrum -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicRegularSpectrum

noncomputable section

/-! The actual complex regular representation of Frobenius satisfies
the Weil norm bound, by the geometric polynomial-height filtration. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped TensorProduct

namespace Construction

universe u

variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]

def frobeniusIntegralLeftMap : Module.End ℤ (Endomorphisms.Construction.AlgebraicEnd A) :=
  LinearMap.mulLeft ℤ (Endomorphisms.Construction.algebraicFrobenius k A)

omit [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem frobeniusIntegralLeftMap_rational :
    (frobeniusIntegralLeftMap k A).baseChange ℚ =
      Algebra.lmul ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) (Endomorphisms.Construction.rationalAlgebraicFrobenius k A) := by
  ext g
  change (1 : ℚ) ⊗ₜ[ℤ] (Endomorphisms.Construction.algebraicFrobenius k A * g) =
    ((1 : ℚ) ⊗ₜ[ℤ] Endomorphisms.Construction.algebraicFrobenius k A) * ((1 : ℚ) ⊗ₜ[ℤ] g)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem frobeniusIntegralLeftMap_complex_eigenvalue_norm
    (z : ℂ) (hz : Module.End.HasEigenvalue ((frobeniusIntegralLeftMap k A).baseChange ℂ) z) :
    ‖z‖ = Real.sqrt (Fintype.card k : ℝ) := by
  have : Module.Finite ℤ (Endomorphisms.Construction.AlgebraicEnd A) := Module.Finite.iff_addGroup_fg.mpr (Endomorphism.FiniteGeneration.Construction.algebraicEnd_finiteGenerated A)
  obtain ⟨d, hd⟩ := IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_degree_bounded k A
  exact PolynomialQuadratic.Construction.PolynomialQuadraticHeight.complexEigenvalue_norm_of_degree_bound d
    (IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight k A) hd (frobeniusIntegralLeftMap k A).toAddMonoidHom
    (Fintype.card k : ℚ) (IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_frobenius_degree_le k A)
    (IntrinsicFrobeniusPolynomialHeight.Construction.nativeEndomorphismPolynomialHeight_frobenius_coeff k A) z hz

theorem frobeniusRationalRegular_complex_eigenvalue_norm
    (z : ℂ) (hz : Module.End.HasEigenvalue
      ((Algebra.lmul ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) (Endomorphisms.Construction.rationalAlgebraicFrobenius k A)).baseChange ℂ) z) :
    ‖z‖ = Real.sqrt (Fintype.card k : ℝ) := by
  rw [← frobeniusIntegralLeftMap_rational] at hz
  exact frobeniusIntegralLeftMap_complex_eigenvalue_norm k A z
    (IntegralQuadraticSpectrum.Construction.eigenvalue_baseChange_of_doubleBaseChange (frobeniusIntegralLeftMap k A) z hz)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicRegularSpectrum
