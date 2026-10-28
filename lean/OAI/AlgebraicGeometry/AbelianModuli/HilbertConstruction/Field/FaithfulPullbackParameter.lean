import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidParameterDiagonal

/-! # Faithful Pullback Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FaithfulPullbackParameter

noncomputable section

/-! Faithfulness on tests whose structural map factors through a given base change implies field faithfulness of the pulled-back parameter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem fieldFaithfulParameter_pullback {S U : Scheme.{u}} (M : Over S) (k : U ⟶ S)
    (h : ∀ (F : Type u) [Field F] (T : Over U) [PreconnectedSpace T.left]
      (s : Spec (.of F) ⟶ T.left) (a b : Over.mk (T.hom ≫ k) ⟶ M),
      s ≫ a.left = s ≫ b.left → a = b) :
    RigidParameterDiagonal.FieldFaithfulParameter ((Over.pullback k).obj M) := by
  intro F _ T _ s a b hab
  let V : Over S := Over.mk (T.hom ≫ k)
  let a' : V ⟶ M := Over.homMk (a.left ≫ pullback.fst M.hom k) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun v => v ≫ k) a.w)
  let b' : V ⟶ M := Over.homMk (b.left ≫ pullback.fst M.hom k) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun v => v ≫ k) b.w)
  have he : a' = b' := h F T s a' b' (by
    change s ≫ (a.left ≫ _) = s ≫ (b.left ≫ _)
    rw [← Category.assoc, ← Category.assoc, hab])
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left he
  · exact a.w.trans b.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FaithfulPullbackParameter
