import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Iso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicFrame

/-! # PD Frame Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDFrameIso

noncomputable section

/-! The actual logarithmic supported residue is preserved by a crystalline
frame isomorphism. Both complexes use the same principal coefficient
category; the target parameters are the literal ambient images. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X} (e : P ≅ Q)

local notation "W" => WittVector p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring

def restriction : ((AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W) ⥤
    (Cᵒᵖ ⥤ ModuleCat.{u} W) :=
  (Functor.whiskeringLeft _ _ _).obj (CrystallinePrincipal.Iso.diagram p k X e).op

instance restriction_additive : (restriction p k X e).Additive where
  map_add := rfl

def restrictionIso : PDComplex.restriction p k X Q ≅ restriction p k X e :=
  (Functor.whiskeringLeft _ _ _).mapIso (NatIso.op (CrystallinePrincipal.Iso.diagramIso p k X e))

def complex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} W) ℕ :=
  ((restriction p k X e).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X)

def complexIso : PDComplex.localizedComplex p k X Q ≅ complex p k X e :=
  (NatIso.mapHomologicalComplex (restrictionIso p k X e) (.up ℕ)).app
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.presheafComplex p k X)

theorem complexIso_hom (q : ℕ) (r : C) :
    ((complexIso p k X e).hom.f q).app (op r) =
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formsPresheaf p k X q).map (CrystallinePrincipal.Iso.map p k X e r).op := rfl

variable (g : ℕ) (a : Fin g → Q.thickening.ring)

def topFrame : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X :=
  (CrystallinePrincipal.Iso.diagram p k X e).obj (PDComplex.topCoefficient p k X Q g a)

def coordinate (i : Fin g) : (topFrame p k X e g a).thickening.ring :=
  (CrystallinePrincipal.Iso.projection p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap
    (e.hom.ambientMap (a i))

theorem map_coordinate (i : Fin g) :
    (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap
      (PDComplex.coordinate p k X Q g a i) = coordinate p k X e g a i :=
  CrystallinePrincipal.Iso.map_algebraMap p k X e _ (a i)

theorem coordinate_isUnit (i : Fin g) : IsUnit (coordinate p k X e g a i) := by
  rw [← map_coordinate]
  exact (PDComplex.coordinate_isUnit p k X Q g a i).map
    (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap

def coordinateUnit (i : Fin g) : (topFrame p k X e g a).thickening.ringˣ :=
  (coordinate_isUnit p k X e g a i).unit

theorem map_coordinateUnit (i : Fin g) :
    Units.map (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap.toMonoidHom
      (PDComplex.coordinateUnit p k X Q g a i) = coordinateUnit p k X e g a i := by
  apply Units.ext
  change (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap
    (↑(PDComplex.coordinateUnit p k X Q g a i) :
      (PDComplex.topFrame p k X Q g a).thickening.ring) = _
  rw [PDComplex.coordinateUnit_val, map_coordinate]
  exact (coordinate_isUnit p k X e g a i).unit_spec.symm

def logarithmicForm : ((complex p k X e).X g).obj (op (PDComplex.topCoefficient p k X Q g a)) :=
  PD.LogarithmicWedges.Forms.logarithmicWedge W (topFrame p k X e g a).thickening.ring
    (RingHom.ker (topFrame p k X e g a).thickening.reduction)
    (topFrame p k X e g a).thickening.dividedPowers g (coordinateUnit p k X e g a)

theorem map_logarithmicForm :
    ((complexIso p k X e).hom.f g).app (op (PDComplex.topCoefficient p k X Q g a))
      (PDComplex.logarithmicForm p k X Q g a) = logarithmicForm p k X e g a := by
  rw [complexIso_hom]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap
    (CommAlgCat.ofHom (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).ambientMap)
    (CrystallinePrincipal.Iso.map p k X e (PDComplex.topCoefficient p k X Q g a)).dp_comp g
    (PD.LogarithmicWedges.Forms.logarithmicWedge _ _ _ _ g _) = _
  rw [PD.LogarithmicFrame.Forms.formMap_logarithmicWedge]
  change PD.LogarithmicWedges.Forms.logarithmicWedge _ _ _ _ g
    (fun i => Units.map _ (PDComplex.coordinateUnit p k X Q g a i)) = _
  have h := funext (map_coordinateUnit p k X e g a)
  exact congrArg (PD.LogarithmicWedges.Forms.logarithmicWedge W
    (topFrame p k X e g a).thickening.ring
    (RingHom.ker (topFrame p k X e g a).thickening.reduction)
    (topFrame p k X e g a).thickening.dividedPowers g) h

theorem logarithmicForm_closed :
    ((complex p k X e).d g (g + 1)).app (op (PDComplex.topCoefficient p k X Q g a))
      (logarithmicForm p k X e g a) = 0 := by
  rw [← map_logarithmicForm]
  exact AugmentedOrdered.CechTopNaturality.mapped_coefficient_closed (PDComplex.family p k X Q g a)
    (complexIso p k X e).hom g (by simp) g _
    (PDComplex.logarithmicForm_closed p k X Q g a)

def total : CochainComplex (ModuleCat.{u} W) ℕ :=
  (AugmentedOrdered.CechFunctor.bicomplex (PDComplex.family p k X Q g a) (complex p k X e)).total (.up ℕ)

def totalMap : PDComplex.total p k X Q g a ⟶ PDFrameIso.total p k X e g a :=
  AugmentedOrdered.CechTopNaturality.totalMap (PDComplex.family p k X Q g a) (complexIso p k X e).hom

def residueClass : (PDFrameIso.total p k X e g a).homology (g + g) :=
  AugmentedOrdered.CechTopTotal.topTotalClass (PDComplex.family p k X Q g a) (complex p k X e)
    g (by simp) g (logarithmicForm p k X e g a) (logarithmicForm_closed p k X e g a)

theorem residueClass_naturality :
    HomologicalComplex.homologyMap (totalMap p k X e g a) (g + g)
      (PDComplex.residueClass p k X Q g a) = residueClass p k X e g a := by
  have h := AugmentedOrdered.CechTopNaturality.topTotalClass_naturality (PDComplex.family p k X Q g a)
    (complexIso p k X e).hom g (by simp) g
    (PDComplex.logarithmicForm p k X Q g a)
    (PDComplex.logarithmicForm_closed p k X Q g a)
  have hf := map_logarithmicForm p k X e g a
  dsimp only [PDComplex.topCoefficient] at hf
  refine h.trans ?_
  apply congrArg (Module.CochainClasses.classMap (PDFrameIso.total p k X e g a) (g + g))
  apply Subtype.ext
  exact congrArg (fun x => AugmentedOrdered.CechTopTotal.topTotalInclusion (PDComplex.family p k X Q g a)
    (complex p k X e) g (by simp) g (g + g) rfl x) hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDFrameIso
