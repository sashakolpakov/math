import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GraphTwisting

/-! # Bundle Graph Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A single power embedding of the external square of a line bundle gives one actual embedded graph Hilbert polynomial for all endomorphisms preserving that bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] {A : Over (Spec (.of K))}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated A.hom]
variable (L : Line.Bundles.LineBundle A.left)
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle L L) (A ⊗ A).hom)

def Common.BundleGraphPolynomial.identityPullbackLineBundleIso : (L.pullback (𝟙 A : A ⟶ A).left).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackId A.left).app L.sheaf

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.tensorSquarePower_hilbertPolynomial_exists :
    ∃ P : Polynomial ℚ, ((L.tensor L).tensorPower E.degree).HasSectionHilbertPolynomial A.hom P := by
  let j := E.relativeMorphism L L
  let i := MorphismGraphFamilies.familyGraph (𝟙 A) ≫ j
  have : IsClosedImmersion j.left := E.closedImmersion
  have : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion ((MorphismGraphFamilies.familyGraph (𝟙 A)).left ≫ j.left))
  obtain ⟨P, hP⟩ := Relative.EmbeddingIntrinsic.relativeEmbedding_intrinsicHilbertPolynomial_exists i
  exact ⟨P, (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso A.hom
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) E.dimension).pullback i.left)
    ((L.tensor L).tensorPower E.degree)
    (E.graphTwistingBundleIso L L (𝟙 A) (Common.BundleGraphPolynomial.identityPullbackLineBundleIso L)) P).mp hP⟩

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.exists_common_graphHilbertPolynomial :
    ∃ P : Polynomial ℚ, ∀ p : A ⟶ A,
      Nonempty ((L.pullback p.left).sheaf ≅ L.sheaf) → Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.relativeMorphism L L) P p := by
  obtain ⟨P, hP⟩ := E.tensorSquarePower_hilbertPolynomial_exists L
  refine ⟨P, fun p hp => ?_⟩
  obtain ⟨e⟩ := hp
  exact (E.graphHilbertPolynomial_iff L L p e P).mpr hP

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
