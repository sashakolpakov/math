import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts

/-! # Embedded Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.EmbeddedBaseChange

noncomputable section

/-! The actual embedded generated family at an affine parameter point commutes with arbitrary coefficient base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ} {R A : CommRingCat.{u}}
variable (x : Spec R ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left) (φ : R ⟶ A)
variable (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

theorem generatedPullbackFamilyAtAffinePoint_baseChange :
    PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (Spec.map φ ≫ x) hB =
      (PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x hB).pullbackAlong
        (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n) := by
  apply Closed.Families.FlatClosedFamily.ext
  have hl := PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal (Spec.map φ ≫ x) hB
  have hr := PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal x hB
  have hm :
      (Truncated.AffineUniversalData.truncatedAffineUniversalData ((Spec.map φ ≫ x) ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).projectiveIdeal =
        (Truncated.AffineUniversalData.truncatedAffineUniversalData (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).projectiveIdeal.comap
          (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) := by
    rw [Category.assoc]
    exact Truncated.AffineUniversalData.truncatedAffineUniversalIdeal_naturality φ (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)
  exact hl.trans (hm.trans (congrArg (fun I => I.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)) hr.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.EmbeddedBaseChange
