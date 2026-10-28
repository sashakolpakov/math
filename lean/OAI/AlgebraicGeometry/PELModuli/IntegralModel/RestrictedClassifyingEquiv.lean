import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.RepresentedBy

/-! # Restricted Classifying Equiv -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictedClassifyingEquiv

noncomputable section

/-! A local representing equivalence is the classifying map of the
restricted global element when their universal classes agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u w
variable {S T : Scheme.{u}} (b : T ⟶ S) (D : Over S)
    (F : (Over S)ᵒᵖ ⥤ Type w) (x : F.obj (.op D))
    (R : ((Over.map b).op ⋙ F).RepresentableBy ((Over.pullback b).obj D))

def restrictedClassifyingEquiv (W : Over T) :
    ((Over.map b).obj W ⟶ D) ≃ F.obj (.op ((Over.map b).obj W)) :=
  ((Over.mapPullbackAdj b).homEquiv W D).trans R.homEquiv

theorem restrictedClassifyingEquiv_apply
    (hx : R.homEquiv (𝟙 ((Over.pullback b).obj D)) =
      F.map ((Over.mapPullbackAdj b).counit.app D).op x)
    (W : Over T) (a : (Over.map b).obj W ⟶ D) :
    restrictedClassifyingEquiv b D F R W a = F.map a.op x := by
  let a' := (Over.mapPullbackAdj b).homEquiv W D a
  have hn : R.homEquiv a' = F.map ((Over.map b).map a').op
      (R.homEquiv (𝟙 ((Over.pullback b).obj D))) := by
    simpa only [Category.comp_id, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] using
      R.homEquiv_comp a' (𝟙 ((Over.pullback b).obj D))
  have hc : (Over.map b).map a' ≫ (Over.mapPullbackAdj b).counit.app D = a :=
    ((Over.mapPullbackAdj b).homEquiv_counit W D a').symm.trans
      (((Over.mapPullbackAdj b).homEquiv W D).symm_apply_apply a)
  change R.homEquiv a' = _
  rw [hn, hx, ← Functor.map_comp_apply, ← op_comp, hc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictedClassifyingEquiv
