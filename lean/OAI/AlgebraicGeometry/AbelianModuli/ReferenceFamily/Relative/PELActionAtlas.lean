import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenPELRepresentations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasProperties
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs

/-! # PEL Action Atlas -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionAtlas.RelativePELActionAtlas

noncomputable section

/-! The actual global bounded parameter scheme obtained by gluing the
constructed affine PEL-action representations of a varying polarized family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    [IsNoetherian M.left] (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x))

def localRepresentation (U : M.left.affineOpens) :
    Open.Representations.OpenRepresentation (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A) U.val :=
  Classical.choose (Affine.OpenPELRepresentations.exists_affine_open_pel_representation P iotaO M A D hc U.val)

theorem local_properties (U : M.left.affineOpens) :
    LocallyOfFiniteType (localRepresentation P iotaO M A D hc U).space.hom ∧
      QuasiCompact (localRepresentation P iotaO M A D hc U).space.hom ∧
      IsSeparated (localRepresentation P iotaO M A D hc U).space.hom :=
  Classical.choose_spec (Affine.OpenPELRepresentations.exists_affine_open_pel_representation P iotaO M A D hc U.val)

def parameter : Over M.left :=
  RepresentationAtlasIs.RepresentationAtlas.over (localRepresentation P iotaO M A D hc)

instance locallyOfFiniteType : LocallyOfFiniteType (parameter P iotaO M A D hc).hom :=
  RepresentationAtlasProperties.RepresentationAtlas.locallyOfFiniteType _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hc U).1)

instance quasiCompact : QuasiCompact (parameter P iotaO M A D hc).hom :=
  RepresentationAtlasProperties.RepresentationAtlas.quasiCompact _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hc U).2.1)

instance separated : IsSeparated (parameter P iotaO M A D hc).hom :=
  RepresentationAtlasProperties.RepresentationAtlas.separated _ (iSup_affineOpens_eq_top M.left)
    (fun U => (local_properties P iotaO M A D hc U).2.2)

instance noetherian : IsNoetherian (parameter P iotaO M A D hc).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
    (parameter P iotaO M A D hc).hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (parameter P iotaO M A D hc).hom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionAtlas.RelativePELActionAtlas
