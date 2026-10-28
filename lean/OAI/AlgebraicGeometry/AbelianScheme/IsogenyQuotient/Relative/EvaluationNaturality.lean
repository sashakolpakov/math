import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative

noncomputable section

section

/-! Evaluate canonical relative product-family comparisons on Noetherian
parameters, preserving their composition laws at every group-factor point. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.comparison_pullHom {T U : Over S} [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] (j : U ⟶ T) (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b)
    (h' : D.relativeValue (j ≫ a) = D.relativeValue (j ≫ b)) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
      (X₁ := B ⊗ A) (X₂ := B ⊗ A)
      (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := b ⊗ₘ 𝟙 A)
      (D.comparison a b h).hom
      (j ⊗ₘ 𝟙 A) ((j ≫ a) ⊗ₘ 𝟙 A) ((j ≫ b) ⊗ₘ 𝟙 A)
      (by simp) (by simp) = (D.comparison (j ≫ a) (j ≫ b) h').hom := by
  rw [← FormalGeometry.Completion.OverLinePullback.Construction.overLineIsoPullbackTo_hom]
  exact congrArg Iso.hom (D.comparison_pullback j a b h h')

set_option backward.isDefEq.respectTransparency false in
def RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison {T : Over S} [IsLocallyNoetherian T.left] (a b : T ⟶ B) (c : T ⟶ A)
    (x y : T ⟶ B ⊗ A) (hx : lift a c = x) (hy : lift b c = y)
    (h : D.relativeValue a = D.relativeValue b) :
    (Scheme.Modules.pullback x.left).obj D.bundle.sheaf ⟶
      (Scheme.Modules.pullback y.left).obj D.bundle.sheaf :=
  pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (X₁ := B ⊗ A) (X₂ := B ⊗ A)
    (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := b ⊗ₘ 𝟙 A)
    (D.comparison a b h).hom
    (lift (𝟙 T) c) x y (by simpa using hx) (by simpa using hy)

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison_self {T : Over S} [IsLocallyNoetherian T.left] (a : T ⟶ B) (c : T ⟶ A)
    (x : T ⟶ B ⊗ A) (hx : lift a c = x) :
    D.evaluateComparison a a c x x hx hx rfl = 𝟙 _ := by
  unfold RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison
  rw [D.comparison_self]
  exact Picard.PoincareBundle.PullHom.pullHom_identity _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison_comp {T : Over S} [IsLocallyNoetherian T.left] (a b d : T ⟶ B) (c : T ⟶ A)
    (x y z : T ⟶ B ⊗ A) (hx : lift a c = x) (hy : lift b c = y) (hz : lift d c = z)
    (hab : D.relativeValue a = D.relativeValue b)
    (hbd : D.relativeValue b = D.relativeValue d) :
    D.evaluateComparison a b c x y hx hy hab ≫ D.evaluateComparison b d c y z hy hz hbd =
      D.evaluateComparison a d c x z hx hz (hab.trans hbd) := by
  unfold RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison
  rw [← Picard.PoincareBundle.PullHom.pullHom_comp]
  exact congrArg (fun e => pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (X₁ := B ⊗ A) (X₂ := B ⊗ A)
    (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf) (f₁ := a ⊗ₘ 𝟙 A) (f₂ := d ⊗ₘ 𝟙 A) e
    (lift (𝟙 T) c) x z (by simpa using hx) (by simpa using hz))
      (congrArg Iso.hom (D.comparison_comp a b d hab hbd))

end

/-! Evaluating a normalized family comparison commutes with pullback
on the test scheme. The two evaluation squares are explicitly pasted. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] (D : RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

set_option backward.isDefEq.respectTransparency false in
theorem RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison_pullback {T U : Over S} [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] (t : U ⟶ T)
    (a b : T ⟶ B) (c : T ⟶ A) (x y : T ⟶ B ⊗ A)
    (hx : lift a c = x) (hy : lift b c = y)
    (x' y' : U ⟶ B ⊗ A) (htx : t ≫ x = x') (hty : t ≫ y = y')
    (hx' : lift (t ≫ a) (t ≫ c) = x') (hy' : lift (t ≫ b) (t ≫ c) = y')
    (h : D.relativeValue a = D.relativeValue b)
    (h' : D.relativeValue (t ≫ a) = D.relativeValue (t ≫ b)) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
        (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
        (f₁ := x) (f₂ := y)
        (D.evaluateComparison a b c x y hx hy h) t x' y' htx hty =
      D.evaluateComparison (t ≫ a) (t ≫ b) (t ≫ c) x' y' hx' hy' h' := by
  have he := congrArg (fun v => pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
    (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
    (f₁ := (t ≫ a) ⊗ₘ 𝟙 A) (f₂ := (t ≫ b) ⊗ₘ 𝟙 A) v
    (lift (𝟙 U) (t ≫ c)) x' y' (by simpa using hx') (by simpa using hy'))
      (D.comparison_pullHom t a b h h')
  rw [pullHom_pullHom] at he
  unfold RigidifiedLine.Construction.RelativeRigidifiedProductLine.evaluateComparison
  rw [pullHom_pullHom]
  have hs : t ≫ lift (𝟙 T) c = lift (𝟙 U) (t ≫ c) ≫ (t ⊗ₘ 𝟙 A) := by simp
  simpa only [hs] using he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative
