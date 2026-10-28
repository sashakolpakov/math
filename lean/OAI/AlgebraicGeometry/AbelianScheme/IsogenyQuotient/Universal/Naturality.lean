import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.EvaluationNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

section

/-! Natural quotient transport is obtained by evaluating the unique
normalized family comparison at the common second coordinate. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q)
  (H : ∀ {T : Over S} (a b : T ⟶ B), a ≫ q = b ≫ q →
    D.relativeValue a = D.relativeValue b)

set_option backward.isDefEq.respectTransparency false in
def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport {T : Over S} (x y : T ⟶ B ⊗ A)
    (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A)) :
    (Scheme.Modules.pullback x.left).obj D.bundle.sheaf ⟶
      (Scheme.Modules.pullback y.left).obj D.bundle.sheaf :=
  D.evaluateUniversalComparison hΓ (x ≫ fst B A) (y ≫ fst B A) (x ≫ snd B A) x y
    (by simp) (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_lift q x y h)
    (H (x ≫ fst B A) (y ≫ fst B A) (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_first q x y h))

set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport_eq_at {T : Over S} (x y : T ⟶ B ⊗ A)
    (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (c : T ⟶ A) (hx : x ≫ snd B A = c) (hy : y ≫ snd B A = c) :
    D.universalQuotientTransport hΓ q H x y h =
      D.evaluateUniversalComparison hΓ (x ≫ fst B A) (y ≫ fst B A) c x y
        (by rw [← hx]; simp) (by rw [← hy]; simp)
        (H (x ≫ fst B A) (y ≫ fst B A) (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_first q x y h)) := by
  subst c
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport_self {T : Over S} (x : T ⟶ B ⊗ A) :
    D.universalQuotientTransport hΓ q H x x rfl = 𝟙 _ :=
  D.evaluateUniversalComparison_self hΓ (x ≫ fst B A) (x ≫ snd B A) x (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport_comp {T : Over S} (x y z : T ⟶ B ⊗ A)
    (hxy : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (hyz : y ≫ (q ⊗ₘ 𝟙 A) = z ≫ (q ⊗ₘ 𝟙 A)) :
    D.universalQuotientTransport hΓ q H x y hxy ≫ D.universalQuotientTransport hΓ q H y z hyz =
      D.universalQuotientTransport hΓ q H x z (hxy.trans hyz) := by
  have hy := (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_second q x y hxy).symm
  have hz := (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_second q x z (hxy.trans hyz)).symm
  rw [D.universalQuotientTransport_eq_at hΓ q H x y hxy (x ≫ snd B A) rfl hy,
    D.universalQuotientTransport_eq_at hΓ q H y z hyz (x ≫ snd B A) hy hz,
    D.universalQuotientTransport_eq_at hΓ q H x z (hxy.trans hyz) (x ≫ snd B A) rfl hz]
  exact D.evaluateUniversalComparison_comp hΓ _ _ _ _ x y z _ _ _ _ _

end

/-! Quotient transport retains the actual geometric pullback maps
between arbitrary test schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{0}} {A B Q : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (q : B ⟶ Q)
  (H : ∀ {T : Over S} (a b : T ⟶ B), a ≫ q = b ≫ q →
    D.relativeValue a = D.relativeValue b)

set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport_pullback {T U : Over S} (t : U ⟶ T)
    (x y : T ⟶ B ⊗ A) (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (x' y' : U ⟶ B ⊗ A) (htx : t ≫ x = x') (hty : t ≫ y = y')
    (h' : x' ≫ (q ⊗ₘ 𝟙 A) = y' ≫ (q ⊗ₘ 𝟙 A)) :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
        (X₁ := B ⊗ A) (X₂ := B ⊗ A) (M₁ := D.bundle.sheaf) (M₂ := D.bundle.sheaf)
        (f₁ := x) (f₂ := y) (D.universalQuotientTransport hΓ q H x y h) t x' y' htx hty =
      D.universalQuotientTransport hΓ q H x' y' h' := by
  subst x'
  subst y'
  have hx : lift (x ≫ fst B A) (x ≫ snd B A) = x := by simp
  have hy := FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_lift q x y h
  have hx' : lift (t ≫ (x ≫ fst B A)) (t ≫ (x ≫ snd B A)) = t ≫ x := by
    rw [← comp_lift, hx]
  have hy' : lift (t ≫ (y ≫ fst B A)) (t ≫ (x ≫ snd B A)) = t ≫ y := by
    rw [← comp_lift, hy]
  have hp : (t ≫ (x ≫ fst B A)) ≫ q = (t ≫ (y ≫ fst B A)) ≫ q := by
    simpa only [Category.assoc] using congrArg (fun a => t ≫ a) (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_first q x y h)
  have hn := D.evaluateUniversalComparison_pullback hΓ t (x ≫ fst B A) (y ≫ fst B A) (x ≫ snd B A)
    x y hx hy (t ≫ x) (t ≫ y) rfl rfl hx' hy'
    (H _ _ (FormalGeometry.Completion.Product.QuotientRelation.Construction.productQuotient_first q x y h)) (H _ _ hp)
  simpa only [Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalQuotientTransport, Category.assoc] using hn

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
