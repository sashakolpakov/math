import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetUnit

/-! # Pullback Forget Adjunction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetAdjunction.Construction

noncomputable section

/-! # Completion: the underlying-set comparison respects inverse-image adjunctions -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Adjunction followed by forgetting agrees with the proved inverse-image comparison. -/
theorem proEtPullbackForgetIso_adjoint
    (P : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (g : (ProetalePullback.Construction.proEtSheafPullback f).obj P ⟶ Q) :
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _
        ((PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app P ≫
          (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map g) =
      (sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).map
        (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv _ _ g) := by
  rw [Adjunction.homEquiv_unit, ← PullbackForgetUnit.Construction.proEtPullbackForgetIso_unit f P,
    Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetAdjunction.Construction
