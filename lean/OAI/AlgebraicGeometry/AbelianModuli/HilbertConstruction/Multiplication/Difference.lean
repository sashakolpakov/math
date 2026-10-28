import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionZeroSection

/-! # Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The difference of two points with the same multiple is a point of the torsion scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.multiplicationDifference (n : ℕ) :
    Limits.pullback (A.multiplication n) (A.multiplication n) ⟶ A.torsionScheme n :=
  (A.torsionSchemePointsEquiv n _).symm
    ⟨pullback.snd (A.multiplication n) (A.multiplication n) / pullback.fst _ _, by
      change (pullback.snd (A.multiplication n) (A.multiplication n) /
        pullback.fst (A.multiplication n) (A.multiplication n)) ^ n = 1
      rw [div_pow, div_eq_one]
      exact (A.comp_multiplication n (pullback.snd _ _)).symm.trans
        (pullback.condition.symm.trans (A.comp_multiplication n (pullback.fst _ _)))⟩

@[reassoc (attr := simp)] theorem Abelian.Schemes.AbelianScheme.multiplicationDifference_inclusion (n : ℕ) :
    A.multiplicationDifference n ≫ A.torsionInclusion n =
      pullback.snd (A.multiplication n) (A.multiplication n) / pullback.fst _ _ :=
  congrArg (fun x : A.torsionPoints n (Limits.pullback (A.multiplication n) (A.multiplication n)) => x.val)
    ((A.torsionSchemePointsEquiv n _).apply_symm_apply _)

theorem Abelian.Schemes.AbelianScheme.multiplicationDifference_diagonal (n : ℕ) :
    pullback.diagonal (A.multiplication n) ≫ A.multiplicationDifference n =
      toUnit A.scheme ≫ A.torsionZeroSection n := by
  apply (cancel_mono (A.torsionInclusion n)).mp
  simp only [Category.assoc, Abelian.Schemes.AbelianScheme.multiplicationDifference_inclusion, Abelian.Schemes.AbelianScheme.torsionZeroSection_inclusion,
    GrpObj.comp_div, pullback.diagonal_fst, pullback.diagonal_snd, MonObj.comp_one, div_self']

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
