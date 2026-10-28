import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

/-! # Hom Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.HomEvaluation

noncomputable section

/-! Every actual section of the coefficient sheaf evaluates internal
Hom on the entire principal-open diagram, by literal restriction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) (x : Γ(M,U))

def component (r : SectionPresheaf.Index U) :
    (SectionPresheaf.modules U hU (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N)).obj (op r) →ₗ[Γ(X,U)]
      (SectionPresheaf.modules U hU N).obj (op r) where
  toFun q := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N (SectionPresheaf.openSubset U r) q
    (M.presheaf.map (SectionPresheaf.inclusion U r).op x)
  map_add' q q' := by
    rw [map_add, LinearMap.add_apply]
  map_smul' a q := by
    change Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N,SectionPresheaf.openSubset U r) at q
    change ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N (SectionPresheaf.openSubset U r)
      ((algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r) a) • q) _ =
        (algebraMap Γ(X,U) Γ(X,SectionPresheaf.openSubset U r) a) • _
    rw [map_smul, LinearMap.smul_apply]

def map : SectionPresheaf.modules U hU (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) ⟶ SectionPresheaf.modules U hU N where
  app r := ModuleCat.ofHom (component U hU M N x r.unop)
  naturality r s a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    have hx : M.presheaf.map (SectionPresheaf.arrow U hU a.unop).op
        (M.presheaf.map (SectionPresheaf.inclusion U r.unop).op x) =
      M.presheaf.map (SectionPresheaf.inclusion U s.unop).op x := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rfl
    have he := Affine.HomEvaluation.restriction M N (SectionPresheaf.openSubset U r.unop)
      (SectionPresheaf.arrow U hU a.unop) q (M.presheaf.map (SectionPresheaf.inclusion U r.unop).op x)
    rw [hx] at he
    exact he

theorem atOne (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N,U)) :
    (HomEvaluation.map U hU M N x).app (op (AtOne.object U))
      (AtOne.equiv U (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) q) =
    AtOne.equiv U N (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U q x) :=
  Affine.HomEvaluation.restriction M N U (SectionPresheaf.inclusion U (AtOne.object U)) q x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.HomEvaluation
