import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CechSquare
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover

/-! # Unit Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.UnitCover.Construction

noncomputable section

/-!
# Completion: the actual affine unit cover and its overlap

For a faithfully flat covering ring map, the adjunction unit gives a
surjective affine cover. Its descent cofaces are its geometric self-pullback.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f))) (A : ProEtale.Algebras.Construction.ProEtaleAlgebra R)

/-- The unit cover is the geometric base change of the given affine covering map. -/
theorem proEtaleUnit_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S ((CommBaseChange.Construction.commAlgExtend f).obj A.obj))))
      ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op).left
      (Spec.map (CommRingCat.ofHom f)) ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).obj (op A)).hom := by
  change IsPullback _ (Spec.map (CommRingCat.ofHom
    (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom.hom.toRingHom))) _ _
  rw [ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CechSquare.Construction.commAlgUnit_isPushout f A.obj)

/-- Faithful flatness makes the actual unit cover surjective. -/
theorem proEtaleUnit_surjective (hflat : f.FaithfullyFlat) :
    Surjective ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op).left :=
  MorphismProperty.of_isPullback (P := @Surjective) (proEtaleUnit_isPullback f hf A)
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hflat).2

/-- The unit cover is quasi-compact because it is a morphism of affine spectra. -/
theorem proEtaleUnit_quasiCompact :
    QuasiCompact ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op).left := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom.hom.toRingHom)))
  infer_instance

/-- The two cofaces of descent describe the actual geometric overlap of the unit cover. -/
theorem proEtaleCech_isPullback :
    IsPullback
      ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app
        ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).obj ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraExtend f).obj A))).op).left
      ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).map
        ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraExtend f).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A))).op).left
      ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op).left
      ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).map ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).op).left := by
  change IsPullback
    (Spec.map (CommRingCat.ofHom (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app
      ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).obj ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraExtend f).obj A))).hom.hom.toRingHom)))
    (Spec.map (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgRestrict f).map ((CommBaseChange.Construction.commAlgExtend f).map
      (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom))).hom.toRingHom)))
    (Spec.map (CommRingCat.ofHom (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom.hom.toRingHom)))
    (Spec.map (CommRingCat.ofHom (((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf).unit.app A).hom.hom.toRingHom)))
  rw [ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit, ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj_unit]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (CechSquare.Construction.commAlgCech_isPushout f A.obj)).flip

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.UnitCover.Construction
