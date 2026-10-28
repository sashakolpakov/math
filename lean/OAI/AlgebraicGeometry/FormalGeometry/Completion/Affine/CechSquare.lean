import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.AlgebraBaseChange
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Cech Square -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CechSquare.Construction

noncomputable section

/-!
# Completion: the actual affine Čech square for tensor base change

The two unit maps in algebra descent form the coordinate-ring pushout
of the covering map with itself. Thus their spectra are the actual overlap.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The adjunction unit is the inclusion of the right tensor factor. -/
theorem commAlgAdj_unit_hom (A : CommAlgCat.{u} R) :
    letI : Algebra R S := f.toAlgebra
    ((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A).hom =
      Algebra.TensorProduct.includeRight := by
  let : Algebra R S := f.toAlgebra
  ext a
  rfl

/-- The actual tensor base-change unit is the lower map in a ring pushout square. -/
theorem commAlgUnit_isPushout (A : CommAlgCat.{u} R) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S ((CommBaseChange.Construction.commAlgExtend f).obj A)))
      (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A).hom.toRingHom)) := by
  let : Algebra R S := f.toAlgebra
  simpa only [commAlgAdj_unit_hom] using! CommRingCat.isPushout_tensorProduct R S A

/-- The two descent cofaces form the actual ring pushout over the local cover. -/
theorem commAlgCech_isPushout (A : CommAlgCat.{u} R) :
    IsPushout
      (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A).hom.toRingHom))
      (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A).hom.toRingHom))
      (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgRestrict f).map ((CommBaseChange.Construction.commAlgExtend f).map
        ((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app A))).hom.toRingHom))
      (CommRingCat.ofHom (((CommBaseChange.Construction.commAlgExtendRestrictAdj f).unit.app
        ((CommBaseChange.Construction.commAlgRestrict f).obj ((CommBaseChange.Construction.commAlgExtend f).obj A))).hom.toRingHom)) := by
  let adj := CommBaseChange.Construction.commAlgExtendRestrictAdj f
  let U := (CommBaseChange.Construction.commAlgRestrict f).obj ((CommBaseChange.Construction.commAlgExtend f).obj A)
  let d := (CommBaseChange.Construction.commAlgExtend f).map (adj.unit.app A)
  have h₁ : CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom ((adj.unit.app A).hom.toRingHom) =
      CommRingCat.ofHom (algebraMap R U) := by
    ext r
    exact (adj.unit.app A).hom.commutes r
  have h₂ : CommRingCat.ofHom (algebraMap S ((CommBaseChange.Construction.commAlgExtend f).obj A)) ≫
      CommRingCat.ofHom (((CommBaseChange.Construction.commAlgRestrict f).map d).hom.toRingHom) =
      CommRingCat.ofHom (algebraMap S ((CommBaseChange.Construction.commAlgExtend f).obj U)) := by
    ext s
    exact d.hom.commutes s
  apply IsPushout.of_top (t := commAlgUnit_isPushout f A)
  · rw [h₁, h₂]
    exact commAlgUnit_isPushout f U
  · exact congrArg (fun g => CommRingCat.ofHom g.hom.toRingHom)
      (adj.unit.naturality (adj.unit.app A)).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CechSquare.Construction
