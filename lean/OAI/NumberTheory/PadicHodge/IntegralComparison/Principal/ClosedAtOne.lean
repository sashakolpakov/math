import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne

/-! # Closed At One -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedAtOne

noncomputable section

/-! The unit principal component of the closed-scheme diagram is the
original section module, linearly over the closed-scheme section ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
variable {X Z : Scheme.{u}} (i : X ⟶ Z) (U : Z.Opens) (M : X.Modules)

instance inclusion_isIso : IsIso (ClosedScalars.pullbackInclusion i U (AtOne.object U)) := by
  have h : ClosedScalars.pullbackInclusion i U (AtOne.object U) =
      (TopologicalSpace.Opens.map i.base).map
        (SectionPresheaf.inclusion U (AtOne.object U)) :=
    Subsingleton.elim _ _
  rw [h]
  infer_instance

def restriction : Γ(M, i ⁻¹ᵁ U) →ₗ[Γ(X, i ⁻¹ᵁ U)]
    Γ(M, ClosedScalars.pullbackOpen i U (AtOne.object U)) where
  toFun := M.presheaf.map (ClosedScalars.pullbackInclusion i U (AtOne.object U)).op
  map_add' := map_add _
  map_smul' a x := by
    exact M.map_smul (ClosedScalars.pullbackInclusion i U (AtOne.object U)) a x

def equiv : Γ(M, i ⁻¹ᵁ U) ≃ₗ[Γ(X, i ⁻¹ᵁ U)]
    Γ(M, ClosedScalars.pullbackOpen i U (AtOne.object U)) :=
  LinearEquiv.ofBijective (restriction i U M)
    (ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (ClosedScalars.pullbackInclusion i U (AtOne.object U)).op))

theorem equiv_apply (x : Γ(M, i ⁻¹ᵁ U)) : equiv i U M x =
    AtOne.equiv U ((Scheme.Modules.pushforward i).obj M) x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedAtOne
