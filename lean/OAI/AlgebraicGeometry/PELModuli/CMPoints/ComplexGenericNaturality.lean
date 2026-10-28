import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralFamily

/-! # Complex Generic Naturality -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexGenericNaturality

noncomputable section

/-! Naturality of the actual complex-to-generic projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def arithmeticComplexGenericProjection {K : Type} [Field K] [NumberField K]
    {κ : K →+* ℂ} (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (X : Over B.base) :
    ((Over.pullback B.complexPoint).obj X).left ⟶ ((Over.pullback B.generic).obj X).left :=
  ((Over.pullbackComp (Spec.map (CommRingCat.ofHom B.embedding)) B.generic).app X).hom.left ≫
    pullback.fst ((Over.pullback B.generic).obj X).hom (Spec.map (CommRingCat.ofHom B.embedding))

theorem arithmeticComplexGenericProjection_naturality
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) {X Y : Over B.base} (f : X ⟶ Y) :
    ((Over.pullback B.complexPoint).map f).left ≫ arithmeticComplexGenericProjection B Y =
    arithmeticComplexGenericProjection B X ≫ ((Over.pullback B.generic).map f).left := by
  let c := Spec.map (CommRingCat.ofHom B.embedding)
  let u := Over.pullbackComp c B.generic
  have hn := congrArg Over.Hom.left (u.hom.naturality f)
  have hp := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst ((Over.pullback B.generic).map f) c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst ((Over.pullback B.generic).obj Y).hom c) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (u.app X).hom.left ≫ k) hp).trans
          (Category.assoc _ _ _).symm)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexGenericNaturality
