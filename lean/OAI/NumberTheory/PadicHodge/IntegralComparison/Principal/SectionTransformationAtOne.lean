import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationExt

/-! # Section Transformation At One -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationAtOne.Ext

noncomputable section

/-! Equality at the literal unit principal open determines a map of
quasicoherent principal section diagrams. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
  (α β : SectionPresheaf.modules U hU M ⟶ SectionPresheaf.modules U hU N)

theorem ext_atOne (h : α.app (op (AtOne.object U)) =
    β.app (op (AtOne.object U))) : α = β := by
  apply SectionTransformationExt.ext U hU M N α β
  let p := terminal.from (AtOne.object U)
  have ha : SectionPresheaf.arrow U hU p = eqToHom
      ((AtOne.open_eq U).trans
        (TerminalScalars.open_eq U hU).symm) := Subsingleton.elim _ _
  have : IsIso (SectionPresheaf.arrow U hU p) := by rw [ha]; infer_instance
  have hinj := (ConcreteCategory.bijective_of_isIso
    (N.presheaf.map (SectionPresheaf.arrow U hU p).op)).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hinj
  have hα := ConcreteCategory.congr_hom (α.naturality p.op) x
  have hβ := ConcreteCategory.congr_hom (β.naturality p.op) x
  change α.app (op (AtOne.object U))
      ((SectionPresheaf.modules U hU M).map p.op x) =
    N.presheaf.map (SectionPresheaf.arrow U hU p).op (α.app (op (⊤_ (SectionPresheaf.Index U))) x) at hα
  change β.app (op (AtOne.object U))
      ((SectionPresheaf.modules U hU M).map p.op x) =
    N.presheaf.map (SectionPresheaf.arrow U hU p).op (β.app (op (⊤_ (SectionPresheaf.Index U))) x) at hβ
  rw [h] at hα
  exact hα.symm.trans hβ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationAtOne.Ext
