import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup

/-! # Pullback Hom Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackHomExt.CM

noncomputable section

/-! Maps into iterated fiber products are determined by their projection
to the original scheme and their already fixed base map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup

universe u
variable {S T U V : Scheme.{u}} (A : Over S)

theorem once (b : T ⟶ S) {X : Over T}
    (f g : X ⟶ (Over.pullback b).obj A)
    (h : f.left ≫ pullback.fst A.hom b = g.left ≫ pullback.fst A.hom b) : f = g := by
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv A b X).injective
  exact Over.OverMorphism.ext h

theorem twice (b : T ⟶ S) (c : U ⟶ T) {X : Over U}
    (f g : X ⟶ (Over.pullback c).obj ((Over.pullback b).obj A))
    (h : (f.left ≫ pullback.fst (pullback.snd A.hom b) c) ≫ pullback.fst A.hom b =
      (g.left ≫ pullback.fst (pullback.snd A.hom b) c) ≫ pullback.fst A.hom b) : f = g := by
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv ((Over.pullback b).obj A) c X).injective
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv A b ((Over.map c).obj X)).injective
  exact Over.OverMorphism.ext h

theorem thrice (b : T ⟶ S) (c : U ⟶ T) (d : V ⟶ U) {X : Over V}
    (f g : X ⟶ (Over.pullback d).obj ((Over.pullback c).obj ((Over.pullback b).obj A)))
    (h : ((f.left ≫ pullback.fst (pullback.snd (pullback.snd A.hom b) c) d) ≫
        pullback.fst (pullback.snd A.hom b) c) ≫ pullback.fst A.hom b =
      ((g.left ≫ pullback.fst (pullback.snd (pullback.snd A.hom b) c) d) ≫
        pullback.fst (pullback.snd A.hom b) c) ≫ pullback.fst A.hom b) : f = g := by
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv ((Over.pullback c).obj ((Over.pullback b).obj A)) d X).injective
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv ((Over.pullback b).obj A) c ((Over.map d).obj X)).injective
  apply (AbelianScheme.TateComparison.Subgroup.pullbackPointsEquiv A b ((Over.map c).obj ((Over.map d).obj X))).injective
  exact Over.OverMorphism.ext h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackHomExt.CM
