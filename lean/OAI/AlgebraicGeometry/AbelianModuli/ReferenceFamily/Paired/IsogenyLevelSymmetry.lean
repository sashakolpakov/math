import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects
import Mathlib.GroupTheory.OrderOfElement

/-! # Isogeny Level Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyLevelSymmetry

noncomputable section

/-! A scalar complement preserves the original ordered level when
its multiplier is one modulo that level. The proof uses the literal
torsion sections on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem paired_quotient_level_relation_symmetric
    {S : Scheme.{0}} {g N n : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (lA : A.FullLevel N) (lB : B.FullLevel N)
    (q : A.scheme ⟶ B.scheme) (v : B.scheme ⟶ A.scheme)
    (hqv : q ≫ v = (𝟙 A.scheme) ^ n) (hn : Nat.ModEq N n 1)
    (hqlevel : ∀ (T : Over S)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (lA.hom.app (.op T) c).val ≫ q = (lB.hom.app (.op T) c).val) :
    ∀ (T : Over S)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (lB.hom.app (.op T) c).val ≫ v = (lA.hom.app (.op T) c).val := by
  intro T c
  rw [← hqlevel T c, Category.assoc, hqv, MonObj.comp_pow, Category.comp_id]
  have ht : ((lA.hom.app (.op T) c).val) ^ N = 1 :=
    (lA.hom.app (.op T) c).property
  exact (pow_eq_pow_of_modEq hn ht).trans (pow_one _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyLevelSymmetry
