import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerComparison

/-! # Arithmetic Tower Coherence -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticTowerCoherence

noncomputable section

/-! The two ways to collapse a finite arithmetic tower have the same
actual comparison map: both are characterized by their projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerComparison

theorem iterated_pullback_associativity
    {S T U V : Scheme} (X : Over S)
    (f : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U)
    (g : U ⟶ S) (t : V ⟶ T) (l : V ⟶ S)
    (wg : h ≫ f = g) (wt : k ≫ h = t) (wl : k ≫ g = l) (wl' : t ≫ f = l) :
    (Over.pullback k).map (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g wg).hom ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X g k l wl).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso ((Over.pullback f).obj X) h k t wt).hom ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f t l wl').hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst]
    have hm := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g wg).hom k
    have hn := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst ((Over.pullback f).obj X) h k t wt
    change ((Over.pullback k).map (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g wg).hom).left ≫
      pullback.fst ((Over.pullback g).obj X).hom k =
        pullback.fst ((Over.pullback h).obj ((Over.pullback f).obj X)).hom k ≫
          (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g wg).hom.left at hm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ pullback.fst X.hom g) hm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a =>
            pullback.fst ((Over.pullback h).obj ((Over.pullback f).obj X)).hom k ≫ a)
              (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X f h g wg)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun a => a ≫ pullback.fst X.hom f) hn.symm)))))
  · exact ((Over.pullback k).map (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f h g wg).hom ≫
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X g k l wl).hom).w.trans
        ((IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso ((Over.pullback f).obj X) h k t wt).hom ≫
          (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X f t l wl').hom).w.symm

theorem arithmetic_tower_complex_comparison
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ)
    (C : IntegralModel.Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    (X : Over (Spec (.of K))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))).map
        ((B.composeSourceNatIso C).app X).hom ≫
          (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso (B.compose C) X).hom =
      (IntegralModel.Arithmetic.TowerComparison.arithmeticTowerComplexSourceIso B C X).hom :=
  iterated_pullback_associativity X B.fieldExtension C.fieldExtension
    (Spec.map (CommRingCat.ofHom C.embedding)) (B.compose C).fieldExtension
    (Spec.map (CommRingCat.ofHom B.embedding)) (Spec.map (CommRingCat.ofHom κ))
    (B.compose_fieldExtension C) (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexBaseEq C)
    (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexBaseEq (B.compose C)) (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexBaseEq B)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticTowerCoherence
