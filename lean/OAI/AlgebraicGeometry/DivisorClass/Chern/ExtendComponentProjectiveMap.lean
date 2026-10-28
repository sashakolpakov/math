import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentOverDesc
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConstantProjectiveMap

/-! # Extend Component Projective Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendComponentProjectiveMap

noncomputable section

/-! Extend an actual projective morphism from one original integral component, using an actual constant morphism on every other component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents P.carrier) {n : ℕ}
  (g : (P.componentVariety C).toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)

def componentProjectiveMapFamily (D : irreducibleComponents P.carrier) :
    (P.componentVariety D).toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver := by
  classical
  exact if h : D = C then h.symm ▸ g else
    ConstantProjectiveMap.constantSchemeMap (P.componentVariety D).presentation (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver
      (ConstantProjectiveMap.projectiveConstantPoint n)

@[simp] theorem componentProjectiveMapFamily_self : componentProjectiveMapFamily P C g C = g := by
  simp [componentProjectiveMapFamily]

theorem componentProjectiveMapFamily_other (D : irreducibleComponents P.carrier) (hDC : D ≠ C) :
    componentProjectiveMapFamily P C g D =
      ConstantProjectiveMap.constantSchemeMap (P.componentVariety D).presentation (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver
        (ConstantProjectiveMap.projectiveConstantPoint n) := by
  simp [componentProjectiveMapFamily, hDC]

def extendComponentProjectiveMap : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver :=
  ComponentOverDesc.componentOverDesc P (componentProjectiveMapFamily P C g)

@[simp] theorem extendComponentProjectiveMap_self :
    P.componentInclusionOver C ≫ extendComponentProjectiveMap P C g = g := by
  rw [extendComponentProjectiveMap, ComponentOverDesc.componentOverDesc_restrict, componentProjectiveMapFamily_self]

theorem extendComponentProjectiveMap_other (D : irreducibleComponents P.carrier) (hDC : D ≠ C) :
    P.componentInclusionOver D ≫ extendComponentProjectiveMap P C g =
      ConstantProjectiveMap.constantSchemeMap (P.componentVariety D).presentation (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver
        (ConstantProjectiveMap.projectiveConstantPoint n) := by
  rw [extendComponentProjectiveMap, ComponentOverDesc.componentOverDesc_restrict, componentProjectiveMapFamily_other P C g D hDC]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendComponentProjectiveMap
