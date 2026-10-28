import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LocalConstancy

/-! # Projective Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every flat projective family over a connected Noetherian scheme has one actual Hilbert polynomial on all field-valued fibers. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem Closed.Families.FlatClosedFamily.exists_connectedFieldHilbertPolynomial
    {S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace S] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n)) :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (F.affineProjectivePullback s).homogeneousIdeal.toIdeal P := by
  let x : S := Classical.ofNonempty
  refine ⟨F.fiberHilbertPolynomial x, fun K _ s => ?_⟩
  apply (F.fieldPoint_hilbertPolynomial_iff s _).mpr
  exact F.fiberHilbertPolynomial_isLocallyConstant.apply_eq_of_isPreconnected
    isPreconnected_univ trivial trivial

theorem Connected.ProjectivePolynomial.graph_exists_connectedNoetherianHilbertPolynomial
    {S : Scheme.{u}} [IsNoetherian S] [ConnectedSpace S] {A B : Over S} {n : ℕ}
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (p : A ⟶ B) :
    ∃ P : Polynomial ℚ, Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P p :=
  ((MorphismGraphFamilies.morphismGraphFamily p).reembed j).exists_connectedFieldHilbertPolynomial

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
