import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.EndomorphismRing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Endomorphism Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Integer scalars in the endomorphism ring recover multiplication on the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

@[simp] theorem Abelian.Schemes.AbelianScheme.endRing_natCast_hom (n : ℕ) :
    (n : A.EndRing).toMul.hom.hom = A.multiplication n := by
  change ((𝟙 A.groupObject) ^ n).hom.hom = A.multiplication n
  rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rfl

theorem Abelian.Schemes.AbelianScheme.endRing_natCast_comp (T : Over S) (x : A.Points T) (n : ℕ) :
    x ≫ (n : A.EndRing).toMul.hom.hom = x ^ n := by
  rw [A.endRing_natCast_hom]
  exact A.comp_multiplication n x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
