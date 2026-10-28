import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.FieldSurjectivity
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Degree Field -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a field, the degree of full-level multiplication equals the rank of its torsion scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem Abelian.Schemes.AbelianScheme.fullLevel_multiplication_finrank_overField (level : A.FullLevel n)
    (x : A.scheme.left) (k : Spec (.of K)) :
    (A.multiplication n).left.finrank x = (A.torsionScheme n).hom.finrank k := by
  have := A.connected_overField
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_isFinite level
  exact ((A.multiplication n).left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace
    x (η[A.scheme].left k)).trans
    (Scheme.Hom.finrank_pullback_snd (A.multiplication n).left η[A.scheme].left k).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
