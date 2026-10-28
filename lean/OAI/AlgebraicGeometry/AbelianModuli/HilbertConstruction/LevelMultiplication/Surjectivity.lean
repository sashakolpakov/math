import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.FieldSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.BaseChange

/-! # Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Residue-field fibers prove surjectivity of full-level multiplication over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_surjective (level : A.FullLevel n) :
    Surjective (A.multiplication n).left := by
  constructor
  intro y
  let K := A.scheme.left.residueField y
  let a : Spec (.of K) ⟶ A.scheme.left := A.scheme.left.fromSpecResidueField y
  let s := a ≫ A.scheme.hom
  let B := A.pullback s
  have := B.fullLevel_multiplication_surjective_overField (level.pullback s)
  let k : Spec (.of K) := Classical.choice inferInstance
  let b : Spec (.of K) ⟶ B.scheme.left :=
    pullback.lift a (𝟙 (Spec (.of K))) (Category.id_comp s).symm
  obtain ⟨z, hz⟩ := (B.multiplication n).left.surjective (b k)
  refine ⟨pullback.fst A.scheme.hom s z, ?_⟩
  have hc := congrArg (fun f : B.scheme.left ⟶ A.scheme.left => f z)
    (A.multiplication_baseChange_fst s n)
  have hb : pullback.fst A.scheme.hom s (b k) = y :=
    (congrArg (fun f : Spec (.of K) ⟶ A.scheme.left => f k)
      (pullback.lift_fst a (𝟙 (Spec (.of K))) (Category.id_comp s).symm)).trans
      (A.scheme.left.fromSpecResidueField_apply y k)
  exact hc.symm.trans ((congrArg (pullback.fst A.scheme.hom s) hz).trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
