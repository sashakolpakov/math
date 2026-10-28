import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismTorsionAction

/-! # Point Groups -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full level identifies the rational torsion group with its finite ordered label group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

def Level.PointGroups.locallyConstantEvaluationEquiv (X : Type u) [TopologicalSpace X] [PreconnectedSpace X]
    (x : X) (G : Type v) [Group G] : LocallyConstant X G ≃* G where
  toFun f := f x
  invFun := LocallyConstant.const X
  left_inv f := by
    apply LocallyConstant.ext
    intro y
    exact f.isLocallyConstant.apply_eq_of_preconnectedSpace x y
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {K : Type u} [Field K] {g N : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))

def Abelian.Schemes.AbelianScheme.fullLevelRationalTorsionEquiv (level : A.FullLevel N) :
    A.torsionPoints N (Over.mk (𝟙 (Spec (.of K)))) ≃*
      Multiplicative (Fin (2 * g) → ZMod N) :=
  (level.app (.op (Over.mk (𝟙 (Spec (.of K)))))).groupIsoToMulEquiv.symm.trans
    (Level.PointGroups.locallyConstantEvaluationEquiv (Spec (.of K)) (Classical.choice inferInstance) _)

theorem Abelian.Schemes.AbelianScheme.fullLevelRationalTorsion_finite [NeZero N] (level : A.FullLevel N) :
    Finite (A.torsionPoints N (Over.mk (𝟙 (Spec (.of K))))) :=
  Finite.of_injective (A.fullLevelRationalTorsionEquiv level)
    (A.fullLevelRationalTorsionEquiv level).injective

theorem Abelian.Schemes.AbelianScheme.fullLevelTorsionEnd_finite [NeZero N] (level : A.FullLevel N) :
    Finite (AddMonoid.End (Additive (A.torsionPoints N (Over.mk (𝟙 (Spec (.of K))))))) := by
  have := A.fullLevelRationalTorsion_finite level
  exact Finite.of_injective DFunLike.coe DFunLike.coe_injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
