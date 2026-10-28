import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Complex Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison.GroupBaseChange

noncomputable section

/-! The exact arithmetic/complex pullback comparison as a natural
isomorphism, so it applies to sections of arbitrary source schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [Field R] [NumberField R] {κ : R →+* ℂ}

def arithmeticComplexNatIso (B : Base.ArithmeticBaseExtension R κ) :
    Over.pullback B.fieldExtension ⋙ Over.pullback (Spec.map (CommRingCat.ofHom B.embedding)) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom κ)) :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexBaseEq B)

theorem arithmeticComplexNatIso_hom_app (B : Base.ArithmeticBaseExtension R κ)
    (X : Over (Spec (.of R))) :
    ((arithmeticComplexNatIso B).app X).hom = (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B X).hom :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso_hom_app B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexBaseEq B) X

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison.GroupBaseChange
