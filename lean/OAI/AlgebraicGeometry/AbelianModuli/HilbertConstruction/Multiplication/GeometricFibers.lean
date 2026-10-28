import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.Cartesian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.RationalFibers

/-! # Geometric Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every algebraically closed field-valued fiber of multiplication is a rational fiber of the corresponding polarized base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.multiplication_geometricFiber_isFinite (n : ℕ) (hn : 0 < n)
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ A.abelian.scheme.left) :
    IsFinite (Limits.pullback.snd (A.abelian.multiplication n).left a) := by
  let s := a ≫ A.abelian.scheme.hom
  let B := A.pullback s
  let b : Spec (.of K) ⟶ B.abelian.scheme.left :=
    Limits.pullback.lift a (𝟙 _) (Category.id_comp s).symm
  have hb : b ≫ B.abelian.scheme.hom = 𝟙 _ := Limits.pullback.lift_snd _ _ _
  let q := Limits.pullback.snd (B.abelian.multiplication n).left b
  have : IsFinite q := B.multiplication_rationalFiber_isFinite n hn b hb
  have H : IsPullback
      (Limits.pullback.fst (B.abelian.multiplication n).left b ≫ Limits.pullback.fst A.abelian.scheme.hom s)
      q (A.abelian.multiplication n).left (b ≫ Limits.pullback.fst A.abelian.scheme.hom s) :=
    (IsPullback.of_hasPullback (B.abelian.multiplication n).left b).paste_horiz
      (A.abelian.multiplication_baseChange_isPullback s n)
  have hbA : b ≫ Limits.pullback.fst A.abelian.scheme.hom s = a := Limits.pullback.lift_fst _ _ _
  have H' : IsPullback
      (Limits.pullback.fst (B.abelian.multiplication n).left b ≫ Limits.pullback.fst A.abelian.scheme.hom s)
      q (A.abelian.multiplication n).left a := hbA ▸ H
  have hq : IsFinite (H'.isoPullback.inv ≫ q) := inferInstance
  exact H'.isoPullback_inv_snd ▸ hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
