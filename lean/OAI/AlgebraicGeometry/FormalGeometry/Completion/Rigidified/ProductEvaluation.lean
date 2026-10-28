import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductComparisonNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback

/-! # Product Evaluation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Evaluate canonical product-family comparisons at an arbitrary
point of the group factor, preserving their composition laws. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

variable {K : Type u} [Field K] [IsAlgClosed K] {A B : Over (Spec (.of K))} [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] (D : ProductLine.Construction.RigidifiedProductLine A B)

theorem ProductLine.Construction.RigidifiedProductLine.comparison_pullHom {T U : Over (Spec (.of K))} (j : U ⟶ T) (a b : T ⟶ B)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (h' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ b))) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
      (X₁ := B ⊗ A) (X₂ := B ⊗ A)
      (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := b ⊗ₘ 𝟙 A)
      (D.comparison a b h).hom
      (j ⊗ₘ 𝟙 A) ((j ≫ a) ⊗ₘ 𝟙 A) ((j ≫ b) ⊗ₘ 𝟙 A)
      (by simp) (by simp) = (D.comparison (j ≫ a) (j ≫ b) h').hom := by
  rw [← OverLinePullback.Construction.overLineIsoPullbackTo_hom]
  exact congrArg Iso.hom (D.comparison_pullback j a b h h')

def ProductLine.Construction.RigidifiedProductLine.evaluateComparison {T : Over (Spec (.of K))} (a b : T ⟶ B) (c : T ⟶ A)
    (x y : T ⟶ B ⊗ A) (hx : lift a c = x) (hy : lift b c = y)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b)) :
    (Scheme.Modules.pullback x.left).obj D.bundle.sheaf ⟶
      (Scheme.Modules.pullback y.left).obj D.bundle.sheaf :=
  pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
    (X₁ := B ⊗ A) (X₂ := B ⊗ A)
    (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := b ⊗ₘ 𝟙 A)
    (D.comparison a b h).hom
    (lift (𝟙 T) c) x y (by simpa using hx) (by simpa using hy)

theorem ProductLine.Construction.RigidifiedProductLine.evaluateComparison_self {T : Over (Spec (.of K))} (a : T ⟶ B) (c : T ⟶ A)
    (x : T ⟶ B ⊗ A) (hx : lift a c = x) :
    D.evaluateComparison a a c x x hx hx rfl = 𝟙 _ := by
  unfold ProductLine.Construction.RigidifiedProductLine.evaluateComparison
  rw [D.comparison_self]
  exact Picard.PoincareBundle.PullHom.pullHom_identity _ _ _

theorem ProductLine.Construction.RigidifiedProductLine.evaluateComparison_comp {T : Over (Spec (.of K))} (a b d : T ⟶ B) (c : T ⟶ A)
    (x y z : T ⟶ B ⊗ A) (hx : lift a c = x) (hy : lift b c = y) (hz : lift d c = z)
    (hab : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b))
    (hbd : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line b) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line d)) :
    D.evaluateComparison a b c x y hx hy hab ≫ D.evaluateComparison b d c y z hy hz hbd =
      D.evaluateComparison a d c x z hx hz (hab.trans hbd) := by
  unfold ProductLine.Construction.RigidifiedProductLine.evaluateComparison
  rw [← Picard.PoincareBundle.PullHom.pullHom_comp]
  exact congrArg (fun e => pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of K)))
    (X₁ := B ⊗ A) (X₂ := B ⊗ A)
    (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := d ⊗ₘ 𝟙 A) e
    (lift (𝟙 T) c) x z (by simpa using hx) (by simpa using hz))
      (congrArg Iso.hom (D.comparison_comp a b d hab hbd))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
