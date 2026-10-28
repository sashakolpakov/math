import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.FamilyDescent

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth Hilbert families over arbitrary rings have canonical finite projective homogeneous quotients in every degree above the uniform bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Flat.ClosedFamilies.FlatClosedHilbertFamily.exists_homogeneousQuotient
    {R : Type u} [CommRing R] {n : ℕ} {P : Polynomial ℚ}
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom]
    (d : ℕ) (hd : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d) :
    ∃ Q : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat,
      Q.toSubmodule = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations F.val.homogeneousIdeal.toIdeal d := by
  obtain ⟨K, _, hK, G, _, hF⟩ := F.exists_smooth_noetherian_hilbert_family
  have : IsNoetherianRing K := hK
  exact F.val.exists_homogeneousQuotient_of_noetherian_model
    (CommRingCat.ofHom K.val.toRingHom) G hF d hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
