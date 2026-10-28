import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverObject

/-! # Site Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteComparison.Construction

noncomputable section

/-! Comparing affine structure maps by the composition law for spectra. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

/-- The identity spectrum map compares the two original-base structure maps. -/
def proEtaleAlgebraSpecRestrictComponent (A : ProEtale.Algebras.Construction.ProEtaleAlgebra S) :
    (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).obj (op ((ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).obj A)) ≅
      ((CoverObject.Construction.affineAlgebraToSlice f hf).obj (op A)).left := by
  refine MorphismProperty.Over.isoMk (Iso.refl (Spec (CommRingCat.of A.obj))) ?_
  change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap S A.obj)) ≫
    Spec.map (CommRingCat.ofHom f)) =
      Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap S A.obj))
  rw [Category.id_comp, Spec.map_comp]

/-- Restriction of scalars and composition of scheme structure maps agree over the original base. -/
def proEtaleAlgebraSpecRestrictIso :
    (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf).op ⋙ ProEtale.Algebras.Construction.proEtaleAlgebraSpec R ≅
      CoverObject.Construction.affineAlgebraToSlice f hf ⋙ Over.forget (CoverObject.Construction.affineCoverObject f hf) :=
  NatIso.ofComponents (fun A => proEtaleAlgebraSpecRestrictComponent f hf A.unop) (by
    intro A B g
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
    rw [Category.id_comp, Category.comp_id])

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteComparison.Construction
