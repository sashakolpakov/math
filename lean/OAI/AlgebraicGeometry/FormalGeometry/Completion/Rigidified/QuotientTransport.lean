import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.EvaluationNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation

/-! # Quotient Transport -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Natural quotient transport is obtained by evaluating the unique
normalized family comparison at the common second coordinate. -/

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

def ProductLine.Construction.RigidifiedProductLine.quotientTransport {T : Over (Spec (.of K))} (x y : T ⟶ B ⊗ A)
    (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A)) :
    (Scheme.Modules.pullback x.left).obj D.bundle.sheaf ⟶
      (Scheme.Modules.pullback y.left).obj D.bundle.sheaf :=
  D.evaluateComparison (x ≫ fst B A) (y ≫ fst B A) (x ≫ snd B A) x y
    (by simp) (Product.QuotientRelation.Construction.productQuotient_lift q x y h)
    (H (x ≫ fst B A) (y ≫ fst B A) (Product.QuotientRelation.Construction.productQuotient_first q x y h))

theorem ProductLine.Construction.RigidifiedProductLine.quotientTransport_eq_at {T : Over (Spec (.of K))} (x y : T ⟶ B ⊗ A)
    (h : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (c : T ⟶ A) (hx : x ≫ snd B A = c) (hy : y ≫ snd B A = c) :
    D.quotientTransport q H x y h =
      D.evaluateComparison (x ≫ fst B A) (y ≫ fst B A) c x y
        (by rw [← hx]; simp) (by rw [← hy]; simp)
        (H (x ≫ fst B A) (y ≫ fst B A) (Product.QuotientRelation.Construction.productQuotient_first q x y h)) := by
  subst c
  rfl

theorem ProductLine.Construction.RigidifiedProductLine.quotientTransport_self {T : Over (Spec (.of K))} (x : T ⟶ B ⊗ A) :
    D.quotientTransport q H x x rfl = 𝟙 _ :=
  D.evaluateComparison_self (x ≫ fst B A) (x ≫ snd B A) x (by simp)

theorem ProductLine.Construction.RigidifiedProductLine.quotientTransport_comp {T : Over (Spec (.of K))} (x y z : T ⟶ B ⊗ A)
    (hxy : x ≫ (q ⊗ₘ 𝟙 A) = y ≫ (q ⊗ₘ 𝟙 A))
    (hyz : y ≫ (q ⊗ₘ 𝟙 A) = z ≫ (q ⊗ₘ 𝟙 A)) :
    D.quotientTransport q H x y hxy ≫ D.quotientTransport q H y z hyz =
      D.quotientTransport q H x z (hxy.trans hyz) := by
  have hy := (Product.QuotientRelation.Construction.productQuotient_second q x y hxy).symm
  have hz := (Product.QuotientRelation.Construction.productQuotient_second q x z (hxy.trans hyz)).symm
  rw [D.quotientTransport_eq_at q H x y hxy (x ≫ snd B A) rfl hy,
    D.quotientTransport_eq_at q H y z hyz (x ≫ snd B A) hy hz,
    D.quotientTransport_eq_at q H x z (hxy.trans hyz) (x ≫ snd B A) rfl hz]
  exact D.evaluateComparison_comp _ _ _ _ x y z _ _ _ _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
