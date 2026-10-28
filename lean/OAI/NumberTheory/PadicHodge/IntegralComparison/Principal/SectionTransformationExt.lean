import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor

/-! # Section Transformation Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationExt

noncomputable section

/-! A transformation between actual quasicoherent principal section
diagrams is determined by its original terminal component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
  (α β : SectionPresheaf.modules U hU M ⟶ SectionPresheaf.modules U hU N)

include hU in
 theorem ext (h : α.app (op (⊤_ (SectionPresheaf.Index U))) = β.app (op (⊤_ (SectionPresheaf.Index U)))) : α = β := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  let rM := AffinePrincipal.Sections.restriction U r.unop.val M
  let rN := AffinePrincipal.Sections.restriction U r.unop.val N
  let : IsLocalizedModule.Away r.unop.val rM :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M ⟨U, hU⟩ r.unop.val
  let : IsLocalizedModule.Away r.unop.val rN :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize N ⟨U, hU⟩ r.unop.val
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.unop.val) rM rN
  apply LinearMap.ext
  intro x
  let p := terminal.from r.unop
  let x₀ : (SectionPresheaf.modules U hU M).obj (op (⊤_ (SectionPresheaf.Index U))) :=
    M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op x
  have hm : (SectionPresheaf.modules U hU M).map p.op x₀ = rM x := by
    change M.presheaf.map (SectionPresheaf.arrow U hU p).op
      (M.presheaf.map (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op x) =
        M.presheaf.map (SectionPresheaf.inclusion U r.unop).op x
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    rfl
  have hα := ConcreteCategory.congr_hom (α.naturality p.op) x₀
  have hβ := ConcreteCategory.congr_hom (β.naturality p.op) x₀
  change α.app r ((SectionPresheaf.modules U hU M).map p.op x₀) =
    (SectionPresheaf.modules U hU N).map p.op (α.app (op (⊤_ (SectionPresheaf.Index U))) x₀) at hα
  change β.app r ((SectionPresheaf.modules U hU M).map p.op x₀) =
    (SectionPresheaf.modules U hU N).map p.op (β.app (op (⊤_ (SectionPresheaf.Index U))) x₀) at hβ
  rw [hm, h] at hα
  rw [hm] at hβ
  exact hα.trans hβ.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationExt
