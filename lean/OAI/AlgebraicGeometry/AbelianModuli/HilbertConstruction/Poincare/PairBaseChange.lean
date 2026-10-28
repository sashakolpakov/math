import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairNaturality

/-! # Pair Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Poincare evaluation at two points commutes with change of base through the actual dual and abelian point equivalences. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S S' : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (c : S' ⟶ S) {T : Over S'}
variable (f : T ⟶ (D.abelian.pullback c).scheme) (a : T ⟶ (A.pullback c).scheme)

theorem Dual.Data.DualAbelianData.poincarePullbackOverMap_pair :
    (Over.map c).map (lift f a) ≫ D.poincarePullbackOverMap c =
      lift (D.abelian.baseChangePointsEquiv c T f) (A.baseChangePointsEquiv c T a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Dual.Data.DualAbelianData.poincarePullbackOverMap_fst,
      lift_fst, Dual.Data.DualAbelianData.baseChangeProjection_comp]
    rw [← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, lift_fst]
  · rw [Category.assoc, Dual.Data.DualAbelianData.poincarePullbackOverMap_snd,
      ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, lift_snd, lift_snd]

def Dual.Data.DualAbelianData.poincarePair_baseChangeIso :
    ((D.pullback c).poincarePair f a).sheaf ≅
      (D.poincarePair (D.abelian.baseChangePointsEquiv c T f)
        (A.baseChangePointsEquiv c T a)).sheaf :=
  (D.pullback c).poincarePairDirectIso f a ≪≫
    (Scheme.Modules.pullbackComp (lift f a).left (D.poincarePullbackOverMap c).left).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (D.poincarePullbackOverMap_pair c f a))).app
      D.poincare.sheaf ≪≫
    (D.poincarePairDirectIso (D.abelian.baseChangePointsEquiv c T f)
      (A.baseChangePointsEquiv c T a)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
