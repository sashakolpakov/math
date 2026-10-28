import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.StalkLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.GermNaturality

/-! # Relative Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.RelativeLifts

noncomputable section

/-! Actual relative lifts on affine source and base schemes are
exactly the relative algebra lifts of their global coordinate rings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineStalkLifts

variable {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (p : X ⟶ Y)
  {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
  {x : X} (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom]

omit [IsAffine X] in
theorem toGlobal_relative_iff (v : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.Lifts J hJ e) :
    v ∈ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p ↔
      ∀ r : Γ(Y, ⊤), (StalkLifts.AffineStalkLifts.toGlobal J hJ e v).hom (p.appTop r) = StalkLifts.AffineStalkLifts.globalMap e (p.appTop r) := by
  constructor
  · intro hv r
    have h := congrArg (fun w : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.Lifts J hJ (p.stalkMap x ≫ e) =>
      w.hom (Y.presheaf.Γgerm (p x) r)) hv
    change v.hom (p.stalkMap x (Y.presheaf.Γgerm (p x) r)) =
      e.hom (p.stalkMap x (Y.presheaf.Γgerm (p x) r)) at h
    rw [HilbertScheme.Presentations.Global.GermNaturality.global_germ_appTop] at h
    exact h
  · intro hv
    let : IsLocalHom (p.stalkMap x ≫ e).hom :=
      inferInstanceAs (IsLocalHom (e.hom.comp (p.stalkMap x).hom))
    apply (StalkLifts.AffineStalkLifts.toGlobal_bijective J hJ (p.stalkMap x ≫ e)).injective
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro r
    change v.hom (p.stalkMap x (Y.presheaf.Γgerm (p x) r)) =
      e.hom (p.stalkMap x (Y.presheaf.Γgerm (p x) r))
    rw [HilbertScheme.Presentations.Global.GermNaturality.global_germ_appTop]
    exact hv r

def relativeEquiv :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := p.appTop.hom.toAlgebra
    letI : Algebra Γ(X, ⊤) C := (StalkLifts.AffineStalkLifts.globalMap e).toAlgebra
    letI : Algebra Γ(Y, ⊤) C := ((StalkLifts.AffineStalkLifts.globalMap e).comp p.appTop.hom).toAlgebra
    letI : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p ≃ₗ[C]
      Relative.LiftDerivations.RelativeLifts.module Γ(Y, ⊤) Γ(X, ⊤) C J hJ := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) C := (StalkLifts.AffineStalkLifts.globalMap e).toAlgebra
  let : Algebra Γ(Y, ⊤) C := ((StalkLifts.AffineStalkLifts.globalMap e).comp p.appTop.hom).toAlgebra
  let : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact {
    toFun := fun v => ⟨StalkLifts.AffineStalkLifts.toGlobal J hJ e v.val, (toGlobal_relative_iff p J hJ e v.val).mp v.property⟩
    invFun := fun w => ⟨(StalkLifts.AffineStalkLifts.equiv J hJ e).symm w.val, by
      apply (toGlobal_relative_iff p J hJ e _).mpr
      have hg := (StalkLifts.AffineStalkLifts.equiv J hJ e).apply_symm_apply w.val
      change StalkLifts.AffineStalkLifts.toGlobal J hJ e ((StalkLifts.AffineStalkLifts.equiv J hJ e).symm w.val) = w.val at hg
      rw [hg]
      exact w.property⟩
    left_inv := fun v => Subtype.ext ((StalkLifts.AffineStalkLifts.equiv J hJ e).symm_apply_apply v.val)
    right_inv := fun w => Subtype.ext ((StalkLifts.AffineStalkLifts.equiv J hJ e).apply_symm_apply w.val)
    map_add' := fun _ _ => Subtype.ext ((StalkLifts.AffineStalkLifts.toGlobal J hJ e).map_add _ _)
    map_smul' := fun _ _ => Subtype.ext ((StalkLifts.AffineStalkLifts.toGlobal J hJ e).map_smul _ _) }

end AffineStalkLifts

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.RelativeLifts
