import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalClosedAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientPolynomialFunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange

/-! # Ambient Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientRepresentation.Core

noncomputable section

/-! An exact polynomial Hilbert representation in a projective ambient
restricts to a projective representation for every closed ambient subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y H : Over S} [IsLocallyNoetherian H.left]

theorem closedAmbient_hilbert_representation
    (BY : Has.Core.ProjectivePresentation Y) (BH : Has.Core.ProjectivePresentation H)
    (i : X ⟶ Y) [IsClosedImmersion i.left] (P : Polynomial ℚ)
    (eH : yoneda.obj H ≅ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BY P).toFunctor) :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧ Has.Core.IsProjectiveOver Z ∧
      ∃ eZ : yoneda.obj Z ≅ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (BY.precompose i) P).toFunctor,
        eZ.hom ≫ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (BY.precompose i) P).ι ≫
          Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i =
            yoneda.map j ≫ eH.hom ≫ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BY P).ι := by
  let t : yoneda.obj H ⟶ Hilbert.Functor.familyFunctor Y :=
    eH.hom ≫ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BY P).ι
  obtain ⟨Z, j, hj, e, he⟩ := NaturalClosedAmbient.Hilbert.naturalFamily_closedAmbient BY i t
  let : IsClosedImmersion j.left := hj
  have hrange : Subfunctor.range t = Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BY P :=
    RepresentedSubfunctorRange.representedSubfunctor_range _ eH
  have h : (Subfunctor.range t).preimage (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i) =
      Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (BY.precompose i) P := by
    rw [hrange]
    ext T F
    exact AmbientFiberPolynomial.Core.hasFiberHilbertPolynomial_pushforward_iff i BY F P
  obtain ⟨eZ, heZ⟩ := RepresentedSubfunctorRange.representedSubfunctor_transport h
    (e.hom ≫ ((Subfunctor.range t).preimage (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i)).ι) e rfl
  refine ⟨Z, j, hj, ⟨BH.precompose j⟩, eZ, ?_⟩
  have hc : eZ.hom ≫ (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (BY.precompose i) P).ι ≫
      Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i =
      e.hom ≫ ((Subfunctor.range t).preimage (Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i)).ι ≫
        Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i := by
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ Hilbert.ClosedAmbientNaturality.closedAmbientTransformation i) heZ
  exact hc.trans he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientRepresentation.Core
