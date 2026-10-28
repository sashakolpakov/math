import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.Difference

/-! # Diagonal Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The diagonal of multiplication is the inverse image of the zero section under the torsion-valued difference map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.multiplicationDifference_isPullback (n : ℕ) :
    IsPullback (toUnit A.scheme) (pullback.diagonal (A.multiplication n))
      (A.torsionZeroSection n) (A.multiplicationDifference n) := by
  apply IsPullback.mk' (A.multiplicationDifference_diagonal n).symm
  · intro T f k _ h
    exact (cancel_mono (pullback.diagonal (A.multiplication n))).mp h
  · intro T a b h
    have hc := congrArg (fun z : T ⟶ A.torsionScheme n => z ≫ A.torsionInclusion n) h
    have hd : b ≫ pullback.snd (A.multiplication n) (A.multiplication n) /
        (b ≫ pullback.fst (A.multiplication n) (A.multiplication n)) = 1 := by
      simpa only [Category.assoc, Abelian.Schemes.AbelianScheme.torsionZeroSection_inclusion, Abelian.Schemes.AbelianScheme.multiplicationDifference_inclusion,
        GrpObj.comp_div, MonObj.comp_one] using hc.symm
    have hb := div_eq_one.mp hd
    refine ⟨b ≫ pullback.fst _ _, toUnit_unique _ _, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hb.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
