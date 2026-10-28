import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison

/-! # Pair Base Change Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection

noncomputable section

/-! The literal projection from a product of base-changed families,
with its two components and the native Poincare projection identified. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {S T : Scheme.{u}} (b : T ⟶ S) (D A : Over S)

def pairBaseChangeProjection :
    ((Over.pullback b).obj D ⊗ (Over.pullback b).obj A).left ⟶ (D ⊗ A).left :=
  (Functor.LaxMonoidal.μ (Over.pullback b) D A).left ≫ pullback.fst (D ⊗ A).hom b

theorem pairBaseChangeProjection_fst :
    pairBaseChangeProjection b D A ≫ (fst D A).left =
      (fst ((Over.pullback b).obj D) ((Over.pullback b).obj A)).left ≫ pullback.fst D.hom b := by
  rw [pairBaseChangeProjection, Category.assoc]
  exact Over.μ_pullback_left_fst_fst D A

theorem pairBaseChangeProjection_snd :
    pairBaseChangeProjection b D A ≫ (snd D A).left =
      (snd ((Over.pullback b).obj D) ((Over.pullback b).obj A)).left ≫ pullback.fst A.hom b := by
  rw [pairBaseChangeProjection, Category.assoc]
  exact Over.μ_pullback_left_fst_snd D A

theorem poincarePullbackOverMap_left {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (P : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    (P.poincarePullbackOverMap b).left = pairBaseChangeProjection b P.abelian.scheme B.scheme := by
  apply Over.tensorObj_ext
  · change (P.poincarePullbackOverMap b ≫ fst P.abelian.scheme B.scheme).left = _
    erw [P.poincarePullbackOverMap_fst, pairBaseChangeProjection_fst]
    simp only [Over.comp_left, Over.map_map_left, AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection,
      AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_apply, Over.id_left, Category.id_comp]
    rfl
  · change (P.poincarePullbackOverMap b ≫ snd P.abelian.scheme B.scheme).left = _
    erw [P.poincarePullbackOverMap_snd, pairBaseChangeProjection_snd]
    exact B.baseChangePointsEquiv_apply b _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection
