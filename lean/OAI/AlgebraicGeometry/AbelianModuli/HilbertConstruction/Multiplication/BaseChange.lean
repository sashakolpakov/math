import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplication by an integer commutes with arbitrary base change as an actual group-scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.multiplication_baseChange (f : T ⟶ S) (n : ℕ) :
    (Over.pullback f).map (A.multiplication n) = (A.pullback f).multiplication n := by
  let U := (A.pullback f).scheme
  let E := A.baseChangePointsMulEquiv f U
  apply E.injective
  calc
    E ((Over.pullback f).map (A.multiplication n)) =
        E (𝟙 U ≫ (Over.pullback f).map (A.multiplication n)) :=
      congrArg E (Category.id_comp _).symm
    _ = E (𝟙 U) ≫ A.multiplication n := Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map (A.multiplication n) f U (𝟙 U)
    _ = E (𝟙 U) ^ n := A.comp_multiplication n (E (𝟙 U))
    _ = E ((A.pullback f).multiplication n) := (map_pow E (𝟙 U) n).symm

theorem Abelian.Schemes.AbelianScheme.multiplication_baseChange_fst (f : T ⟶ S) (n : ℕ) :
    ((A.pullback f).multiplication n).left ≫ Limits.pullback.fst A.scheme.hom f =
      Limits.pullback.fst A.scheme.hom f ≫ (A.multiplication n).left := by
  rw [← A.multiplication_baseChange f n]
  exact Limits.pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
