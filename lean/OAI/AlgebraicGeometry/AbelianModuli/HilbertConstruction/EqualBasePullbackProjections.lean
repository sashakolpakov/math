import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapPullback

/-! # Equal Base Pullback Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualBasePullbackProjections

noncomputable section

/-! The comparison induced by equal base maps preserves the original-family projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem equalBasePullback_hom_fst {S T : Scheme.{u}} (A : Over S)
    (f g : T ⟶ S) (h : f = g) :
    (eqToIso (congrArg (fun b => (Over.pullback b).obj A) h)).hom.left ≫ pullback.fst A.hom g =
      pullback.fst A.hom f := by
  subst g
  change (𝟙 _ : pullback A.hom f ⟶ pullback A.hom f) ≫ pullback.fst A.hom f = _
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualBasePullbackProjections
