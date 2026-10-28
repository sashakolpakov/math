import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleClasses
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group

/-! # Frobenius Pairing -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPairing

noncomputable section

/-!
# Homomorphisms: Frobenius pullback of a pairing line bundle

Relative Frobenius respects the canonical product comparison for base
change. Thus the simultaneous Frobenius pullback of a line bundle on a
product, in particular a Poincare bundle, is its p-th tensor power.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits hiding prodComparison prodComparison_fst prodComparison_snd
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)

def frobeniusTwistProductIso (A B : Over S) :
    Frobenius.Construction.frobeniusTwist p hp hS A ⊗ Frobenius.Construction.frobeniusTwist p hp hS B ≅
      Frobenius.Construction.frobeniusTwist p hp hS (A ⊗ B) :=
  (asIso (prodComparison (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) A B)).symm

theorem relativeFrobenius_prodComparison (A B : Over S) :
    Frobenius.Construction.relativeFrobenius p hp hS (A ⊗ B) ≫
        prodComparison (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) A B =
      Frobenius.Construction.relativeFrobenius p hp hS A ⊗ₘ Frobenius.Construction.relativeFrobenius p hp hS B := by
  apply CartesianMonoidalCategory.hom_ext
  · erw [Category.assoc, prodComparison_fst, tensorHom_fst]
    exact ((Group.Construction.relativeFrobeniusNat p hp hS).naturality (fst A B)).symm
  · erw [Category.assoc, prodComparison_snd, tensorHom_snd]
    exact ((Group.Construction.relativeFrobeniusNat p hp hS).naturality (snd A B)).symm

theorem relativeFrobenius_product (A B : Over S) :
    (Frobenius.Construction.relativeFrobenius p hp hS A ⊗ₘ Frobenius.Construction.relativeFrobenius p hp hS B) ≫
        (frobeniusTwistProductIso p hp hS A B).hom =
      Frobenius.Construction.relativeFrobenius p hp hS (A ⊗ B) := by
  rw [← relativeFrobenius_prodComparison]
  change (Frobenius.Construction.relativeFrobenius p hp hS (A ⊗ B) ≫ _) ≫
    inv (prodComparison (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) A B) = _
  erw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Projection from the product of Frobenius twists to the original product. -/
def frobeniusTwistProductProjection (A B : Over S) :
    (Frobenius.Construction.frobeniusTwist p hp hS A ⊗ Frobenius.Construction.frobeniusTwist p hp hS B).left ⟶ (A ⊗ B).left :=
  (frobeniusTwistProductIso p hp hS A B).hom.left ≫
    pullback.fst (A ⊗ B).hom (Frobenius.Construction.absoluteFrobenius p hp S hS)

theorem relativeFrobenius_product_projection (A B : Over S) :
    (Frobenius.Construction.relativeFrobenius p hp hS A ⊗ₘ Frobenius.Construction.relativeFrobenius p hp hS B).left ≫
        frobeniusTwistProductProjection p hp hS A B =
      Frobenius.Construction.absoluteFrobenius p hp (A ⊗ B).left (Frobenius.Construction.prime_eq_zero_of_map p hS (A ⊗ B).hom) := by
  change _ ≫ ((frobeniusTwistProductIso p hp hS A B).hom.left ≫ _) = _
  rw [← Category.assoc, ← Over.comp_left, relativeFrobenius_product,
    Frobenius.Construction.relativeFrobenius_comp_fst]

/-- The simultaneous relative Frobenius formula for a line bundle on a product. -/
def frobeniusPairingPullbackIso (A B : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ B).left) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (Frobenius.Construction.relativeFrobenius p hp hS A ⊗ₘ Frobenius.Construction.relativeFrobenius p hp hS B).left
      (P.pullback (frobeniusTwistProductProjection p hp hS A B))).sheaf ≅
        (LineBundleTensor.Construction.tensorPowerLineBundle P p).sheaf :=
  (Scheme.Modules.pullbackComp
    (Frobenius.Construction.relativeFrobenius p hp hS A ⊗ₘ Frobenius.Construction.relativeFrobenius p hp hS B).left
    (frobeniusTwistProductProjection p hp hS A B)).app P.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (relativeFrobenius_product_projection p hp hS A B)).app P.sheaf ≪≫
    LineBundleTensor.Construction.frobeniusPullbackLineBundleIso p hp (Frobenius.Construction.prime_eq_zero_of_map p hS (A ⊗ B).hom) P

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPairing
