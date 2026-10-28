import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkRegular
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence

/-! # Point Algebra -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra

noncomputable section

/-! The actual stalk evaluation at a scheme-valued point is an
augmentation for the canonical coefficient-field action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

abbrev scalarAlgebra (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x (by trivial)).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra

theorem germ_evaluation (p : Spec (.of K) ⟶ X) :
    X.presheaf.germ ⊤ (p (IsLocalRing.closedPoint K)) trivial ≫ Scheme.stalkClosedPointTo p =
      p.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
  simpa using Scheme.germ_stalkClosedPointTo p ⊤ trivial

def evaluation (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    letI := scalarAlgebra f (p (IsLocalRing.closedPoint K))
    X.presheaf.stalk (p (IsLocalRing.closedPoint K)) →ₐ[K] K := by
  let := scalarAlgebra f (p (IsLocalRing.closedPoint K))
  refine { (Scheme.stalkClosedPointTo p).hom with commutes' := ?_ }
  intro c
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo p) c = c
  rw [germ_evaluation, ← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hp]
  simp

theorem evaluation_apply (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (r : X.presheaf.stalk (p (IsLocalRing.closedPoint K))) :
    evaluation f p hp r = Scheme.stalkClosedPointTo p r := rfl

theorem finite_cotangent (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    letI := scalarAlgebra f (p (IsLocalRing.closedPoint K))
    Module.Finite K (AugmentedCotangent.ideal (evaluation f p hp)).Cotangent := by
  let := scalarAlgebra f (p (IsLocalRing.closedPoint K))
  let := Smooth.StalkRegular.stalk_regular f m (p (IsLocalRing.closedPoint K))
  exact AugmentedRegularJet.finite_cotangent (evaluation f p hp)

theorem jet_dimension (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hd : Order.coheight (p (IsLocalRing.closedPoint K)) = m) :
    letI := scalarAlgebra f (p (IsLocalRing.closedPoint K))
    Module.finrank K (K × (AugmentedCotangent.ideal (evaluation f p hp)).Cotangent) = m + 1 := by
  let := scalarAlgebra f (p (IsLocalRing.closedPoint K))
  let := Smooth.StalkRegular.stalk_regular f m (p (IsLocalRing.closedPoint K))
  apply AugmentedRegularJet.jet_dimension (evaluation f p hp) m
  rw [ringKrullDim_stalk_eq_coheight, hd]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra
