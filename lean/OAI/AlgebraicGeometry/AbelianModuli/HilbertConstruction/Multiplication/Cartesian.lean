import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.BaseChange

/-! # Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The base-change compatibility of multiplication forms a cartesian square of schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}}

theorem Multiplication.Cartesian.overPullback_morphism_isPullback {X Y : Over S} (p : X ⟶ Y) (f : T ⟶ S) :
    IsPullback (Limits.pullback.fst X.hom f) ((Over.pullback f).map p).left
      p.left (Limits.pullback.fst Y.hom f) := by
  have hrectangle : IsPullback (Limits.pullback.fst X.hom f)
      (((Over.pullback f).map p).left ≫ ((Over.pullback f).obj Y).hom)
      (p.left ≫ Y.hom) f := by
    exact (congrArg₂ (fun (a : Limits.pullback X.hom f ⟶ T) (b : X.left ⟶ S) =>
      IsPullback (Limits.pullback.fst X.hom f) a b f)
      ((Over.pullback f).map p).w.symm p.w.symm).mp (IsPullback.of_hasPullback X.hom f)
  exact IsPullback.of_bot hrectangle (Limits.pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback Y.hom f)

theorem Abelian.Schemes.AbelianScheme.multiplication_baseChange_isPullback {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (f : T ⟶ S) (n : ℕ) :
    IsPullback (Limits.pullback.fst A.scheme.hom f) ((A.pullback f).multiplication n).left
      (A.multiplication n).left (Limits.pullback.fst A.scheme.hom f) := by
  rw [← A.multiplication_baseChange f n]
  exact Multiplication.Cartesian.overPullback_morphism_isPullback (A.multiplication n) f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
