import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Tower
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

/-! # Tower Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerComparison

noncomputable section

/-! Exact source and section comparisons over a finite arithmetic tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

def arithmeticTowerComplexSourceIso (B : Base.ArithmeticBaseExtension K κ)
    (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    (X : Over (Spec (.of K))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))).obj
        ((Over.pullback C.fieldExtension).obj ((Over.pullback B.fieldExtension).obj X)) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X :=
  (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C).app ((Over.pullback B.fieldExtension).obj X) ≪≫
    (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X

theorem arithmeticTowerComplexSourceIso_point (B : Base.ArithmeticBaseExtension K κ)
    (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    {X : Over (Spec (.of K))} (x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X) :
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom C.embedding)))
      (Section.Comparisons.mappedSection (Over.pullback C.fieldExtension)
        (Section.Comparisons.mappedSection (Over.pullback B.fieldExtension) x₀)) ≫
        (arithmeticTowerComplexSourceIso B C X).hom =
          Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom κ))) x₀ := by
  let P := Over.pullback B.fieldExtension
  let Q := Over.pullback C.fieldExtension
  let F := Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))
  let G := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))
  let H := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  have hC : Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection P x₀)) ≫
      ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C).app (P.obj X)).hom =
        Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection P x₀) := Section.Comparisons.mappedSection_comp_naturality Q F G
          (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C).hom (Section.Comparisons.mappedSection P x₀)
  have hB : Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection P x₀) ≫
      ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X).hom = Section.Comparisons.mappedSection H x₀ :=
    Section.Comparisons.mappedSection_comp_naturality P G H (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).hom x₀
  change Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection P x₀)) ≫
    ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C).app (P.obj X)).hom ≫
      ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X).hom = _
  rw [← Category.assoc, hC]
  exact hB

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerComparison
