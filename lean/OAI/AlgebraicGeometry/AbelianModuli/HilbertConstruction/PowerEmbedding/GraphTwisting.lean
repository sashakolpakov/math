import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Graph Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! In a projective embedding defined by a power of an external tensor product, a bundle-preserving morphism graph pulls O(1) back to the corresponding power of the source tensor square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B : Over S} (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left)
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle L M) (A ⊗ B).hom)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.relativeMorphism : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S E.dimension :=
  SectionsProjectiveMorphism.sectionProjectiveMorphism (A ⊗ B).hom E.sections E.covers

instance Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.relativeMorphism_closed : IsClosedImmersion (E.relativeMorphism L M).left :=
  E.closedImmersion

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.externalPowerIso :
    E.power.sheaf ≅ ((Graph.ExternalTensorBundle.externalTensorBundle L M).tensorPower E.degree).sheaf :=
  (E.isPower.unique ((Graph.ExternalTensorBundle.externalTensorBundle L M).tensorPower_isTensorPower E.degree)).some

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.graphTwistingBundleIso (p : A ⟶ B)
    (e : (M.pullback p.left).sheaf ≅ L.sheaf) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension).pullback (MorphismGraphFamilies.familyGraph p ≫ E.relativeMorphism L M).left).sheaf ≅
      ((L.tensor L).tensorPower E.degree).sheaf := by
  let g := (MorphismGraphFamilies.familyGraph p).left
  let j := (E.relativeMorphism L M).left
  let T := Graph.ExternalTensorBundle.externalTensorBundle L M
  exact (Scheme.Modules.pullbackComp g j).symm.app (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension).sheaf ≪≫
    (Scheme.Modules.pullback g).mapIso (E.twistingBundleIso (A ⊗ B).hom ≪≫ E.externalPowerIso L M) ≪≫
    T.powerBaseChangeIso g E.degree ≪≫
    (TensorPower.Maps.tensorPowerFunctor A.left E.degree).mapIso (Graph.ExternalTensorBundle.graphExternalTensorBundleIsoOfPreserves p L M e)

variable {K : Type u} [Field K] {C D : Over (Spec (.of K))}
variable [Flat C.hom] [LocallyOfFinitePresentation C.hom] [IsSeparated D.hom]

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.graphHilbertPolynomial_iff
    (L : Line.Bundles.LineBundle C.left) (M : Line.Bundles.LineBundle D.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle L M) (C ⊗ D).hom)
    (p : C ⟶ D) (e : (M.pullback p.left).sheaf ≅ L.sheaf) (P : Polynomial ℚ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.relativeMorphism L M) P p ↔
      ((L.tensor L).tensorPower E.degree).HasSectionHilbertPolynomial C.hom P :=
  (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff (E.relativeMorphism L M) P p).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso C.hom
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) E.dimension).pullback
        (MorphismGraphFamilies.familyGraph p ≫ E.relativeMorphism L M).left)
      ((L.tensor L).tensorPower E.degree) (E.graphTwistingBundleIso L M p e) P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
