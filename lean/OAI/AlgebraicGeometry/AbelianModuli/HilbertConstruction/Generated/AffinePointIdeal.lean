import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedUniversality

/-! # Affine Point Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.AffinePointIdeal

noncomputable section

/-! The finite quotient data at an arbitrary affine generated-parameter point have exactly the pulled-back family's ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem generatedAffinePoint_data_projectiveIdeal
    {R : CommRingCat.{u}} {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ}
    (f : Spec R ⟶ S) (x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N)
    (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    ((Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f).symm x).val.projectiveIdeal =
      (PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat).ideal := by
  let D := (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f).symm x
  have hx : Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f D = x :=
    (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f).apply_symm_apply x
  have hd := FamilyClassification.truncatedGeneratedClassifier_data f D
  rw [hx] at hd
  have h := PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal x.left hflat
  rw [hd] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.AffinePointIdeal
