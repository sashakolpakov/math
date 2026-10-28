import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarLeviNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators

/-! # Weighted Fresnel Matrices -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelMatrices.Construction

noncomputable section

/-! The weighted Fourier-quadratic matrix relation and its exact
localization at every place. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarLeviNormalization.LocalAnalysis

def scalarSymmetricMatrix (k : Type) [Field k] (N : ℕ) (b : k) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N :=
  ⟨b • 1, Matrix.isSymm_one.smul b⟩

theorem weighted_fresnel_symplectic_relation (k : Type) [Field k] (N : ℕ) (b : k) (hb : b ≠ 0) :
    Local.Generators.Construction.weylSymplectic k N * Local.Generators.Construction.quadraticSymplectic (scalarSymmetricMatrix k N b) * Local.Generators.Construction.weylSymplectic k N =
      Local.Generators.Construction.quadraticSymplectic (scalarSymmetricMatrix k N (-b⁻¹)) * Local.Generators.Construction.leviSymplectic (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb) *
        Local.Generators.Construction.weylSymplectic k N * Local.Generators.Construction.quadraticSymplectic (scalarSymmetricMatrix k N (-b⁻¹)) := by
  apply Subtype.ext
  have he : (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb).val = b • (1 : Matrix (Fin N) (Fin N) k) := by
    ext i j
    simp [ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hi : ((ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)⁻¹).val = b⁻¹ • (1 : Matrix (Fin N) (Fin N) k) := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin N) (Units.mk0 b hb))⁻¹).val = _
    rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  change (Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 (b • 1) 1) * Matrix.fromBlocks 0 1 (-1) 0 =
    ((Matrix.fromBlocks 1 0 ((-b⁻¹) • 1) 1 * Matrix.fromBlocks (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb).val 0 0
      ((ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb)⁻¹).val.transpose) * Matrix.fromBlocks 0 1 (-1) 0) *
        Matrix.fromBlocks 1 0 ((-b⁻¹) • 1) 1
  rw [he, hi]
  simp [Matrix.fromBlocks_multiply, smul_smul, hb]

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem localizeScalarSymmetricMatrix (b : F) (v : ArchimedeanAdeles.Construction.Places F) :
    QuadraticGenerators.Construction.localizeQuadratic F N (scalarSymmetricMatrix F N b) v =
      scalarSymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N (ArchimedeanAdeles.Construction.rationalScalar F v b) := by
  apply Subtype.ext
  ext i j
  simp [QuadraticGenerators.Construction.localizeQuadratic, scalarSymmetricMatrix, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

theorem localizeScalarLinearMatrix (b : F) (hb : b ≠ 0) (v : ArchimedeanAdeles.Construction.Places F) :
    Rational.Construction.localizeLinear F N (ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N b hb) v = ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix N (ArchimedeanAdeles.Construction.rationalScalar F v b)
      (by simpa only [map_zero] using (ArchimedeanAdeles.Construction.rationalScalar F v).injective.ne hb) := by
  apply Units.ext
  ext i j
  simp [Rational.Construction.localizeLinear, ScalarLeviNormalization.LocalAnalysis.scalarLinearMatrix, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedFresnelMatrices.Construction
