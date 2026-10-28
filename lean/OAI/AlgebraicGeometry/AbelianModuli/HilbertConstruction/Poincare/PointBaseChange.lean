import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBundle

/-! # Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual Poincare line bundle of a rational dual point pulls back to the bundle of the base-changed point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K K' : Type u} [Field K] [Field K'] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
variable (c : Spec (.of K') ⟶ Spec (.of K))
variable (x : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme)

def Dual.Data.DualAbelianData.poincarePointBundle_baseChangeIso :
    ((D.pullback c).poincarePointBundle (D.abelian.basePointPullback c x)).sheaf ≅
      ((D.poincarePointBundle x).pullback (pullback.fst A.scheme.hom c)).sheaf := by
  let A' := (A.pullback c).scheme
  let p := Dual.Data.DualAbelianData.baseChangeProjection A c
  have hp : p.left = pullback.fst A.scheme.hom c := by
    change (𝟙 A'.left) ≫ pullback.fst A.scheme.hom c = _
    exact Category.id_comp _
  have hu : (Over.map c).map (toUnit A') ≫ Base.PointChange.baseChangeUnitMap c = p ≫ toUnit A.scheme := by
    apply Over.OverMorphism.ext
    exact p.w.symm
  have hx : D.abelian.baseChangePointsEquiv c A'
        (toUnit A' ≫ D.abelian.basePointPullback c x) = p ≫ (toUnit A.scheme ≫ x) := by
    rw [Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp,
      Abelian.Schemes.AbelianScheme.basePointPullback_comparison, ← Category.assoc, hu, Category.assoc]
  let e := D.poincarePair_baseChangeIso c (toUnit A' ≫ D.abelian.basePointPullback c x) (𝟙 A')
  change ((D.pullback c).poincarePointBundle (D.abelian.basePointPullback c x)).sheaf ≅
    (D.poincarePair (D.abelian.baseChangePointsEquiv c A'
      (toUnit A' ≫ D.abelian.basePointPullback c x)) p).sheaf at e
  rw [hx] at e
  have e' : ((D.poincarePointBundle x).pullback p.left).sheaf ≅
      (D.poincarePair (p ≫ (toUnit A.scheme ≫ x)) p).sheaf := by
    simpa only [Dual.Data.DualAbelianData.poincarePointBundle, Category.comp_id] using
      D.poincarePairPullbackIso (toUnit A.scheme ≫ x) (𝟙 A.scheme) p
  rw [← hp]
  exact e ≪≫ e'.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
