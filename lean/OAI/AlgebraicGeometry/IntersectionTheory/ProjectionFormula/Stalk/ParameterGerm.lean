import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization

/-! # Parameter Germ -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ParameterGerm

noncomputable section

/-! A global affine parameter commutes with the actual localization
from a scheme stalk to a prime of that stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

def globalSection {Z : Scheme} (t : Z ⟶ Spec (.of ℂ[X])) (a : ℂ) : Γ(Z, ⊤) :=
  t.appTop ((Scheme.ΓSpecIso (.of ℂ[X])).inv (Polynomial.X - Polynomial.C a))

theorem global_germ {Z : Scheme} (t : Z ⟶ Spec (.of ℂ[X])) (a : ℂ) (x : Z) :
    Z.presheaf.germ ⊤ x trivial (globalSection t a) = Affine.ParameterFiber.germ ℂ t x a := by
  change (t.app ⊤ ≫ Z.presheaf.germ (t ⁻¹ᵁ ⊤) x trivial)
    ((Scheme.ΓSpecIso (.of ℂ[X])).inv (Polynomial.X - Polynomial.C a)) = _
  rw [← Scheme.Hom.germ_stalkMap t ⊤ x trivial]
  rfl

theorem global_localization (Z : Scheme) (x : Z) (p : PrimeSpectrum (Z.presheaf.stalk x))
    (s : Γ(Z, ⊤)) :
    (Z.fromSpecStalk x).stalkMap p (Z.presheaf.germ ⊤ (Z.fromSpecStalk x p) trivial s) =
      StructureSheaf.toStalk (Z.presheaf.stalk x) p (Z.presheaf.germ ⊤ x trivial s) := by
  change (Z.presheaf.germ ⊤ (Z.fromSpecStalk x p) trivial ≫ (Z.fromSpecStalk x).stalkMap p) s = _
  rw [Scheme.Hom.germ_stalkMap, Scheme.fromSpecStalk_app (show x ∈ (⊤ : Z.Opens) from trivial)]
  simp only [Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem localization {Z : Scheme} (t : Z ⟶ Spec (.of ℂ[X])) (a : ℂ) (x : Z)
    (p : PrimeSpectrum (Z.presheaf.stalk x)) :
    (Z.fromSpecStalk x).stalkMap p
      (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a) =
        StructureSheaf.toStalk (Z.presheaf.stalk x) p (Affine.ParameterFiber.germ ℂ t x a) := by
  rw [← global_germ t a (Z.fromSpecStalk x p), ← global_germ t a x]
  exact global_localization Z x p (globalSection t a)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ParameterGerm
