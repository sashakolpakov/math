import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.DegreeField
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsionDegree
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.Cartesian

/-! # Degree -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full-level multiplication has constant degree N^(2g) over every base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {g n : ℕ} [NeZero n] (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_finrank (level : A.FullLevel n) (y : A.scheme.left) :
    (A.multiplication n).left.finrank y = n ^ (2 * g) := by
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_isFinite level
  let K := A.scheme.left.residueField y
  let a : Spec (.of K) ⟶ A.scheme.left := A.scheme.left.fromSpecResidueField y
  let s := a ≫ A.scheme.hom
  let B := A.pullback s
  let k : Spec (.of K) := Classical.choice inferInstance
  let b : Spec (.of K) ⟶ B.scheme.left :=
    pullback.lift a (𝟙 (Spec (.of K))) (Category.id_comp s).symm
  have hb : pullback.fst A.scheme.hom s (b k) = y :=
    (congrArg (fun f : Spec (.of K) ⟶ A.scheme.left => f k)
      (pullback.lift_fst a (𝟙 (Spec (.of K))) (Category.id_comp s).symm)).trans
      (A.scheme.left.fromSpecResidueField_apply y k)
  have h := Scheme.Hom.finrank_of_isPullback (pullback.fst A.scheme.hom s)
    (B.multiplication n).left (A.multiplication n).left (pullback.fst A.scheme.hom s)
    (A.multiplication_baseChange_isPullback s n) (b k)
  have hB : (B.multiplication n).left.finrank (b k) = n ^ (2 * g) :=
    (B.fullLevel_multiplication_finrank_overField (level.pullback s) (b k) k).trans
      (B.fullLevel_torsion_finrank (level.pullback s) k)
  exact ((congrArg (A.multiplication n).left.finrank hb).symm.trans h.symm).trans hB

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
