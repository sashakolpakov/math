import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OpenRepresentations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlasProperties
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasCoverValues

/-! # Action Atlas -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionAtlas

noncomputable section

/-! The actual global bounded parameter scheme obtained by gluing the
constructed affine PEL-action representations of a varying polarized family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace RelativePELActionAtlas
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    [IsNoetherian M.left] (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x))

def localRepresentation (U : M.left.affineOpens) :
    Reduced.OpenRepresentations.ReducedOpenRepresentation (ActionFunctor.relativePELActionFunctor P iotaO M A) U.val :=
  Classical.choose (Affine.OpenRepresentations.exists_affine_open_pel_representation P iotaO M A D hPresentations hc U.val)

theorem local_properties (U : M.left.affineOpens) :
    LocallyOfFiniteType (localRepresentation P iotaO M A D hPresentations hc U).space.hom ∧
      QuasiCompact (localRepresentation P iotaO M A D hPresentations hc U).space.hom ∧
      IsSeparated (localRepresentation P iotaO M A D hPresentations hc U).space.hom :=
  Classical.choose_spec (Affine.OpenRepresentations.exists_affine_open_pel_representation P iotaO M A D hPresentations hc U.val)

def parameter : Over M.left :=
  Reduced.RepresentationAtlas.ReducedRepresentationAtlas.over (localRepresentation P iotaO M A D hPresentations hc)

instance reduced : IsReduced (parameter P iotaO M A D hPresentations hc).left :=
  inferInstanceAs (IsReduced (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.scheme
    (localRepresentation P iotaO M A D hPresentations hc)))

instance locallyOfFiniteType : LocallyOfFiniteType (parameter P iotaO M A D hPresentations hc).hom :=
  Reduced.RepresentationAtlasProperties.ReducedRepresentationAtlas.locallyOfFiniteType _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hPresentations hc U).1)

instance quasiCompact : QuasiCompact (parameter P iotaO M A D hPresentations hc).hom :=
  Reduced.RepresentationAtlasProperties.ReducedRepresentationAtlas.quasiCompact _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hPresentations hc U).2.1)

instance separated : IsSeparated (parameter P iotaO M A D hPresentations hc).hom :=
  Reduced.RepresentationAtlasProperties.ReducedRepresentationAtlas.separated _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hPresentations hc U).2.2)

instance noetherian : IsNoetherian (parameter P iotaO M A D hPresentations hc).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
    (parameter P iotaO M A D hPresentations hc).hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (parameter P iotaO M A D hPresentations hc).hom

end RelativePELActionAtlas

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionAtlas
