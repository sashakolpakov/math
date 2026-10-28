import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration

/-! # Levi Conjugation -/

namespace OAI.RepresentationTheory.Theta.Adelic.LeviConjugation

noncomputable section

/-! Fourier conjugation and reciprocal positive factors for inverse
transpose Levi matrices, using the actual Haar modulus normalization. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest.Construction

def inverseTranspose {k : Type} [Field k] {N : ℕ} (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N where
  val := (A⁻¹).val.transpose
  inv := A.val.transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

theorem determinantUnit_inverseTranspose
    {k : Type} [NormedField k] {N : ℕ} (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) :
    Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (inverseTranspose A) = (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)⁻¹ := by
  apply Units.ext
  change (A⁻¹).val.transpose.det = _
  rw [Matrix.det_transpose]
  rfl

theorem weyl_conjugate_levi {k : Type} [Field k] {N : ℕ} (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) :
    Weil.Local.Generators.Construction.weylSymplectic k N * Weil.Local.Generators.Construction.leviSymplectic A * (Weil.Local.Generators.Construction.weylSymplectic k N)⁻¹ =
      Weil.Local.Generators.Construction.leviSymplectic (inverseTranspose A) := by
  apply Subtype.ext
  change (Weil.Local.Generators.Construction.weylSymplectic k N).val * (Weil.Local.Generators.Construction.leviSymplectic A).val * ((Weil.Local.Generators.Construction.weylSymplectic k N)⁻¹).val = _
  rw [SymplecticGroup.coe_inv]
  simp [Weil.Local.Generators.Construction.weylSymplectic_matrix, Weil.Local.Generators.Construction.leviSymplectic, inverseTranspose, Matrix.J,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem localizeLinear_inverseTranspose
    (F : Type) [Field F] [NumberField F] (N : ℕ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Weil.AdelicSplitting.Rational.Construction.localizeLinear F N (inverseTranspose A) v = inverseTranspose (Weil.AdelicSplitting.Rational.Construction.localizeLinear F N A v) := by
  apply Units.ext
  ext i j
  rfl

theorem rationalLeviCoefficient_inverseTranspose
    (F : Type) [Field F] [NumberField F] (N : ℕ) (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient F N (inverseTranspose A) v = (Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient F N A v)⁻¹ := by
  unfold Weil.AdelicSplitting.ThetaTest.Construction.rationalLeviCoefficient
  rw [localizeLinear_inverseTranspose, determinantUnit_inverseTranspose, Weil.Local.FunctionsMetaplectic.Construction.localModulus_inv, Real.sqrt_inv]

end

end OAI.RepresentationTheory.Theta.Adelic.LeviConjugation
