import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.LocalPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ClosedFamilyPullbacks

/-! # Relative Local Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual smooth closed family in relative projective space over any local ring has one Hilbert polynomial on every field-valued fiber. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Closed.Families.FlatClosedFamily.smooth_exists_localFieldHilbertPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n)) [Smooth F.scheme.hom] :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ Spec (.of R)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback x).homogeneousIdeal.toIdeal P := by
  let G := F.affineProjectivePullback (𝟙 _)
  have : Smooth G.scheme.hom := F.affineProjectivePullback_smooth (𝟙 _)
  obtain ⟨P, hP⟩ := G.smooth_exists_localCoefficientFieldHilbertPolynomial
  refine ⟨P, fun K _ x => ?_⟩
  let φ : CommRingCat.of R ⟶ CommRingCat.of K := (Spec.fullyFaithful.preimage x).unop
  have he : Spec.map φ = x := Spec.fullyFaithful.map_preimage x
  have hx := F.affineProjectivePullback_coefficient (𝟙 _) φ
  have hc : Spec.map φ ≫ 𝟙 (Spec (.of R)) = x := (Category.comp_id _).trans he
  have hF := (congrArg (fun a => F.affineProjectivePullback a) hc).symm.trans hx
  rw [hF]
  exact hP K φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
