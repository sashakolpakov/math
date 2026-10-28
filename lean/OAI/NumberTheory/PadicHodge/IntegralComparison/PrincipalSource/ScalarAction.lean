import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenFixedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedAtOne

/-! # Scalar Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ScalarAction

noncomputable section

/-! The scalar action on the original nested source diagram is literal
multiplication by the restricted source function. It multiplies the
numerator of the original section map on the whole principal diagram. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)
  (z : Γ(Y, (f ≫ i) ⁻¹ᵁ U))

theorem atOne (x : Γ(N, (f ≫ i) ⁻¹ᵁ U)) :
    (OpenFixedClass.scalar f i U hU N z).app
        (op (Principal.AtOne.object U)) (Principal.AtOne.equiv U (OpenRestriction.image f i N) x) =
      Principal.AtOne.equiv U (OpenRestriction.image f i N) (z • x) := by
  rw [OpenFixedClass.scalar_app]
  exact (N.map_smul (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U
    (Principal.AtOne.object U)) z x).symm

theorem symbol (ω : Γ(N, (f ≫ i) ⁻¹ᵁ U)) :
    Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj N) ω ≫
        OpenFixedClass.scalar f i U hU N z =
      Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj N) (z • ω) := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (OpenFixedClass.scalar f i U hU N z).app r
    ((Principal.PushforwardSection.map i U hU ((Scheme.Modules.pushforward f).obj N) ω).app r x) = _
  rw [OpenFixedClass.scalar_app]
  change (Y.presheaf.map (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U r.unop).op z) •
      ((show Γ(Y, Principal.ClosedScalars.pullbackOpen (f ≫ i) U r.unop) from
          f.app (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r.unop) x) •
        N.presheaf.map (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U r.unop).op ω) =
    (show Γ(Y, Principal.ClosedScalars.pullbackOpen (f ≫ i) U r.unop) from
        f.app (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r.unop) x) •
      N.presheaf.map (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U r.unop).op (z • ω)
  rw [N.map_smul]
  exact smul_comm _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ScalarAction
