import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSection

/-! # Pushforward Section Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionNaturality

noncomputable section

/-! Multiplication by an actual local section commutes with every
morphism of coefficient sheaves on the entire principal-open diagram. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Z : Scheme.{u}} (i : X ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
  {M N : X.Modules} (a : M ⟶ N) (ω : Γ(M, i ⁻¹ᵁ U))

theorem map :
    PushforwardSection.map i U hU M ω ≫
        SectionPresheaf.moduleHom U hU ((Scheme.Modules.pushforward i).map a) =
      PushforwardSection.map i U hU N (a.app (i ⁻¹ᵁ U) ω) := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(X, i ⁻¹ᵁ SectionPresheaf.openSubset U r.unop) at x
  change a.app (i ⁻¹ᵁ SectionPresheaf.openSubset U r.unop)
      (x • M.presheaf.map (PushforwardSection.sourceInclusion i U r.unop).op ω) =
    x • N.presheaf.map (PushforwardSection.sourceInclusion i U r.unop).op
      (a.app (i ⁻¹ᵁ U) ω)
  rw [Scheme.Modules.Hom.app_smul]
  exact congrArg (x • ·) (PresheafOfModules.naturality_apply a.val
    (PushforwardSection.sourceInclusion i U r.unop).op ω)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionNaturality
