import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.QuotientTransport

/-! # Quotient Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Quotient transport retains all original geometric pullback maps
on arbitrary test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {K : Type u} [Field K] [IsAlgClosed K] {A B Q : Over (Spec (.of K))} [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] (D : ProductLine.Construction.RigidifiedProductLine A B) (q : B ⟶ Q)
  (H : ∀ {T : Over (Spec (.of K))} (a b : T ⟶ B), a ≫ q = b ≫ q →
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))

theorem ProductLine.Construction.RigidifiedProductLine.quotientTransport_pullback {T U : Over (Spec (.of K))} (t : U ⟶ T)
    (x y : T ⟶ B ⊗ A) (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (x' y' : U ⟶ B ⊗ A) (htx : t ≫ x = x') (hty : t ≫ y = y')
    (h' : x' ≫ (q ⊗ₘ 𝟙 A) = y' ≫ (q ⊗ₘ 𝟙 A)) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
        (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
        (f₁ := x) (f₂ := y) (D.quotientTransport q H x y h) t x' y' htx hty =
      D.quotientTransport q H x' y' h' := by
  subst x'
  subst y'
  have hx : lift (x ≫ fst B A) (x ≫ snd B A) = x := by simp
  have hy := Product.QuotientRelation.Construction.productQuotient_lift q x y h
  have hx' : lift (t ≫ (x ≫ fst B A)) (t ≫ (x ≫ snd B A)) = t ≫ x := by
    rw [← comp_lift, hx]
  have hy' : lift (t ≫ (y ≫ fst B A)) (t ≫ (x ≫ snd B A)) = t ≫ y := by
    rw [← comp_lift, hy]
  have hp : (t ≫ (x ≫ fst B A)) ≫ q = (t ≫ (y ≫ fst B A)) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun a => t ≫ a) (Product.QuotientRelation.Construction.productQuotient_first q x y h)
  have hn := D.evaluateComparison_pullback t (x ≫ fst B A) (y ≫ fst B A) (x ≫ snd B A)
    x y hx hy (t ≫ x) (t ≫ y) rfl rfl hx' hy'
    (H _ _ (Product.QuotientRelation.Construction.productQuotient_first q x y h)) (H _ _ hp)
  simpa only [ProductLine.Construction.RigidifiedProductLine.quotientTransport, Category.assoc] using hn

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
