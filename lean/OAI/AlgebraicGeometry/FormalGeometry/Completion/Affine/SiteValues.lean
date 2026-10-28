import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteComparison

/-! # Site Values -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteValues.Construction

noncomputable section

/-! Values of actual pro-étale presheaves on affine algebras and their comparison. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

variable (F : (Spec (CommRingCat.of R)).ProEtᵒᵖ ⥤ Type w)

/-- The actual presheaf evaluated on spectra of weakly étale algebras. -/
def proEtaleAffineValues : ProEtale.Algebras.Construction.ProEtaleAlgebra R ⥤ Type w :=
  (opOpEquivalence (ProEtale.Algebras.Construction.ProEtaleAlgebra R)).inverse ⋙ (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).op ⋙ F

/-- Values obtained by passing through the covering object's slice site. -/
def affineSliceValues : ProEtale.Algebras.Construction.ProEtaleAlgebra S ⥤ Type w :=
  (opOpEquivalence (ProEtale.Algebras.Construction.ProEtaleAlgebra S)).inverse ⋙ (CoverObject.Construction.affineAlgebraToSlice f hf).op ⋙
    (Over.forget (CoverObject.Construction.affineCoverObject f hf)).op ⋙ F

/-- The affine slice values are the actual values after scalar restriction. -/
def affineSliceValuesIso :
    affineSliceValues f hf F ≅ ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf ⋙ proEtaleAffineValues F :=
  NatIso.ofComponents (fun A => F.mapIso ((SiteComparison.Construction.proEtaleAlgebraSpecRestrictIso f hf).app (op A)).op)
    (by
      intro A B g
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      apply F.congr_map
      exact congrArg Quiver.Hom.op ((SiteComparison.Construction.proEtaleAlgebraSpecRestrictIso f hf).hom.naturality g.op).symm)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SiteValues.Construction
