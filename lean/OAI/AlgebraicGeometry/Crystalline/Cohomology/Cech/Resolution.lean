import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafQuasi

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution.CechResolution

noncomputable section

/-!
# The canonical Čech sheaf resolution

The restriction augmentation of the actual Čech sheaf complex is a
quasi-isomorphism for every open cover. The proof uses its canonical
local contraction and detects cohomology isomorphisms on the cover.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

theorem quasiIso_map_of_natIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (F G : CochainComplex A ℕ ⥤ CochainComplex B ℕ)
    (e : F ≅ G) {K L : CochainComplex A ℕ} (f : K ⟶ L) [QuasiIso (F.map f)] :
    QuasiIso (G.map f) :=
  quasiIso_of_arrow_mk_iso (F.map f) (G.map f)
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.CechPresheaf.Presheaves R X)

theorem restricted_sheafAugmentation_quasiIso (i : ι) :
    QuasiIso (((Cover.CechRestriction.sheafRestrictionFunctor R (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.sheafAugmentation R X U P)) := by
  let G := Cover.CechRestriction.restrictionFunctor R (U i).ι
  let S := Presheaf.CechPresheaf.sheafification R (U i).toScheme
  let a := Presheaf.CechPresheaf.augmentation R X U P
  have : QuasiIso (((G ⋙ S).mapHomologicalComplex (ComplexShape.up ℕ)).map a) := by
    change QuasiIso ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map a))
    rw [← AugmentationRestriction.CechAugmentationRestriction.restrictedHomotopyHom R P U i]
    exact HomotopyEquiv.quasiIso_hom (S.mapHomotopyEquiv
      (AugmentationRestriction.CechAugmentationRestriction.restrictedHomotopyEquiv R P U i))
  exact quasiIso_map_of_natIso _ _ (Cover.CechRestriction.sheafificationComplexIso R (U i).ι) a

/-- The canonical Čech augmentation is a quasi-isomorphism for an open cover. -/
theorem augmentation_quasiIso (hU : iSup U = ⊤) :
    QuasiIso (Presheaf.CechPresheaf.sheafAugmentation R X U P) :=
  SheafQuasi.SheafQuasiIsoLocality.quasiIso_of_restrictions R X U hU
    (Presheaf.CechPresheaf.sheafAugmentation R X U P)
    (fun i => restricted_sheafAugmentation_quasiIso R X U P i)

/-- Degree-zero Čech cohomology is the coefficient sheaf. -/
def degreeZeroHomologyIso (hU : iSup U = ⊤) :
    (Presheaf.CechPresheaf.sheafComplex R X U P).homology 0 ≅
      (Presheaf.CechPresheaf.sheafification R X).obj P := by
  have : QuasiIsoAt (Presheaf.CechPresheaf.sheafAugmentation R X U P) 0 :=
    (augmentation_quasiIso R X U P hU).quasiIsoAt 0
  exact (isoOfQuasiIsoAt (Presheaf.CechPresheaf.sheafAugmentation R X U P) 0).symm ≪≫
    ((HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex
      (Presheaf.CechPresheaf.sheafification R X) (ComplexShape.up ℕ) 0).app P)).toHomologyIso 0) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          ((Presheaf.CechPresheaf.sheafification R X).obj P)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution.CechResolution
