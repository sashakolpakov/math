import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductEvaluation

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Evaluating a normalized family comparison commutes with pullback
on the test scheme. The two evaluation squares are explicitly pasted. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Over (Spec (.of K))} [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] (D : ProductLine.Construction.RigidifiedProductLine A B)

theorem ProductLine.Construction.RigidifiedProductLine.evaluateComparison_pullback {T U : Over (Spec (.of K))} (t : U ⟶ T)
    (a b : T ⟶ B) (c : T ⟶ A) (x y : T ⟶ B ⊗ A)
    (hx : lift a c = x) (hy : lift b c = y)
    (x' y' : U ⟶ B ⊗ A) (htx : t ≫ x = x') (hty : t ≫ y = y')
    (hx' : lift (t ≫ a) (t ≫ c) = x') (hy' : lift (t ≫ b) (t ≫ c) = y')
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (h' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (t ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (t ≫ b))) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
        (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
        (f₁ := x) (f₂ := y)
        (D.evaluateComparison a b c x y hx hy h) t x' y' htx hty =
      D.evaluateComparison (t ≫ a) (t ≫ b) (t ≫ c) x' y' hx' hy' h' := by
  have he := congrArg (fun v => pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
    (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
    (f₁ := (t ≫ a) ⊗ₘ 𝟙 A) (f₂ := (t ≫ b) ⊗ₘ 𝟙 A) v
    (lift (𝟙 U) (t ≫ c)) x' y' (by simpa using hx') (by simpa using hy'))
      (D.comparison_pullHom t a b h h')
  rw [pullHom_pullHom] at he
  unfold ProductLine.Construction.RigidifiedProductLine.evaluateComparison
  rw [pullHom_pullHom]
  have hs : t ≫ lift (𝟙 T) c = lift (𝟙 U) (t ≫ c) ≫ (t ⊗ₘ 𝟙 A) := by simp
  simpa only [hs] using he

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
