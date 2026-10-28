import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit

/-! # Section Coefficient Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SectionCoefficientUnit

noncomputable section

/-! Evaluation along a section of a finite coefficient scheme preserves
the original global and Čech units, including the direct-image composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {T Y X Z S : Scheme.{u}} (s : T ⟶ Y) (f : Y ⟶ X) (i : X ⟶ Z) (π : Z ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens) (hU : iSup U = ⊤)

def sheafMap : StructurePullbackUnit.coefficients f i ⟶
    StructurePullbackUnit.coefficients (s ≫ f) i :=
  (pushforward i).map
    ((pushforward f).map (SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom) ≫
      (pushforwardComp s f).hom.app (SheafOfModules.unit T.ringCatSheaf))

theorem section_map_one :
    (OrderedCech.Augmentation.sections π).map (sheafMap s f i)
      (show (OrderedCech.Augmentation.sections π).obj
        (StructurePullbackUnit.coefficients f i) from (1 : Γ(Y, ⊤))) =
      (1 : Γ(T, ⊤)) := by
  change s.appTop.hom 1 = 1
  exact s.appTop.hom.map_one

theorem preserves_unit :
    HomologicalComplex.homologyMap
      ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map (sheafMap s f i)) 0
      (StructurePullbackUnit.unit f i π U hU) =
        StructurePullbackUnit.unit (s ≫ f) i π U hU := by
  have h := ConcreteCategory.congr_hom
    (ZeroSections.naturality π U hU (sheafMap s f i))
    (show (OrderedCech.Augmentation.sections π).obj
      (StructurePullbackUnit.coefficients f i) from (1 : Γ(Y, ⊤)))
  change (ZeroSections.iso π U hU
      (StructurePullbackUnit.coefficients (s ≫ f) i)).hom
      ((OrderedCech.Augmentation.sections π).map (sheafMap s f i) (1 : Γ(Y, ⊤))) =
    HomologicalComplex.homologyMap
      ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map (sheafMap s f i)) 0
      (StructurePullbackUnit.unit f i π U hU) at h
  rw [section_map_one] at h
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SectionCoefficientUnit
