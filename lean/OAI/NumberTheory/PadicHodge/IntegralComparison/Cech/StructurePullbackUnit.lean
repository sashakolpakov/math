import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructureUnit

/-! # Structure Pullback Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit

noncomputable section

/-! Pullback of regular functions preserves the actual degree-zero
Čech unit, including after a further direct image. This is the unit
compatibility used in the normalized Serre trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

universe u

variable {Y X Z S : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) (π : Z ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens) (hU : iSup U = ⊤)

abbrev coefficients :=
  (pushforward i).obj ((pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))

def sheafMap : Global.StructureUnit.directImage i ⟶ coefficients f i :=
  (pushforward i).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

def unit : (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (coefficients f i) U).homology 0 :=
  (ZeroSections.iso π U hU (coefficients f i)).hom
    (show (OrderedCech.Augmentation.sections π).obj (coefficients f i)
      from (1 : Γ(Y, ⊤)))

theorem section_map_one :
    (OrderedCech.Augmentation.sections π).map (sheafMap f i)
      (show (OrderedCech.Augmentation.sections π).obj (Global.StructureUnit.directImage i)
        from (1 : Γ(X, ⊤))) = (1 : Γ(Y, ⊤)) := by
  change f.appTop.hom 1 = 1
  exact f.appTop.hom.map_one

theorem preserves_unit :
    HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map (sheafMap f i)) 0
      (StructureUnit.unit i π U hU) = StructurePullbackUnit.unit f i π U hU := by
  have h := ConcreteCategory.congr_hom
    (ZeroSections.naturality π U hU (sheafMap f i))
    (show (OrderedCech.Augmentation.sections π).obj (Global.StructureUnit.directImage i)
      from (1 : Γ(X, ⊤)))
  change (ZeroSections.iso π U hU (coefficients f i)).hom
      ((OrderedCech.Augmentation.sections π).map (sheafMap f i) (1 : Γ(X, ⊤))) =
    HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map (sheafMap f i)) 0
      (StructureUnit.unit i π U hU) at h
  rw [section_map_one] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit
