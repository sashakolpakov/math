import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormPurity
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault

/-! # Dolbeault Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultRealization.Smooth

noncomputable section

/-! The actual algebraic realization is annihilated by the genuine antiholomorphic differential. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (φ a))

include hc in
theorem smoothFormMap_derivative_character (n : ℕ) (a : Algebraic.Forms.Form A n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a)) =
      AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter n 0 • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a) := by
  apply Subtype.ext
  change Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a)).val =
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter n 0 • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a)).val
  have h := (Holomorphic.FormPurity.Smooth.smoothFormMap_pure φ hφ hc (n + 1) (Algebraic.Forms.differential A n a)).complexAction_eq
    (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)
  simpa only [Smooth.CochainMap.smoothFormMap_d, inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter] using h

theorem pureSmoothFormMap_doublePrime_projection (n : ℕ) (a : Algebraic.Forms.Form A n) :
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M n 0 (Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc n a) = 0 := by
  rw [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm_apply]
  change (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a) -
      (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter n 0)⁻¹ •
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)
          (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a))) = 0
  rw [smoothFormMap_derivative_character φ hφ hc, smul_smul,
    inv_mul_cancel₀ (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter_ne_zero n 0), one_smul, sub_self, smul_zero]

theorem pureSmoothFormMap_dDoublePrime (n : ℕ) (a : Algebraic.Forms.Form A n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc n a) = 0 := by
  apply Subtype.ext
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, pureSmoothFormMap_doublePrime_projection]
  rfl

theorem pureSmoothFormMap_dPrime (n : ℕ) (a : Algebraic.Forms.Form A n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc n a) =
      Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc (n + 1) (Algebraic.Forms.differential A n a) := by
  apply Subtype.ext
  have h := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc n a)
  rw [pureSmoothFormMap_dDoublePrime] at h
  simp only [ZeroMemClass.coe_zero, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self, add_zero] at h
  change (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Holomorphic.FormPurity.Smooth.pureSmoothFormMap φ hφ hc n a)).val =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Smooth.CochainMap.smoothFormMap φ hφ n a) at h
  exact h.trans (Smooth.CochainMap.smoothFormMap_d φ hφ n a).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultRealization.Smooth
