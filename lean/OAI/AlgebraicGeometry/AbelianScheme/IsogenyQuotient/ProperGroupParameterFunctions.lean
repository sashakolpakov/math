import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness

/-! # Proper Group Parameter Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperGroupParameterFunctions.Construction

noncomputable section

/-! Proper-group global functions remain constant in the group
coordinate after an arbitrary parameter change and an affine test over
that parameter. The comparison uses actual iterated fiber-product maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem properGroup_parameter_product_appTop_isIso {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (Q : Over (Spec (.of k))) (K : Over Q.left) [IsAffine K.left] :
    IsIso (fst K ((Over.pullback Q.hom).obj A)).left.appTop := by
  let A' := (Over.pullback Q.hom).obj A
  let R : Over (Spec (.of k)) := Over.mk (K.hom ≫ Q.hom)
  have : IsAffine R.left := inferInstanceAs (IsAffine K.left)
  have : IsIso ((Over.pullback R.hom).obj A).hom.appTop :=
    CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A R
  let e : (Over.pullback R.hom).obj A ≅ (Over.pullback K.hom).obj A' :=
    (Over.pullbackComp K.hom Q.hom).app A
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget K.left).map e.inv))
  have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.left.op))
  have : IsIso ((Over.pullback K.hom).obj A').hom.appTop := by
    rw [← e.inv.w, Scheme.Hom.comp_appTop]
    infer_instance
  let b := pullbackSymmetry K.hom A'.hom
  have : IsIso b.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map b.hom.op))
  have hb : b.hom ≫ ((Over.pullback K.hom).obj A').hom = (fst K A').left :=
    pullbackSymmetry_hom_comp_snd K.hom A'.hom
  change IsIso (fst K A').left.appTop
  rw [← hb, Scheme.Hom.comp_appTop]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperGroupParameterFunctions.Construction
