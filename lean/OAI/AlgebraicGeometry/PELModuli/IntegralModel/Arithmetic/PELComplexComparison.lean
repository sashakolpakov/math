import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericFamilyComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison

/-! # PEL Complex Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual integral PEL spread has the supplied reference's complex
reduction as its complex fiber, with the composed coefficient embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def PEL.Has.IntegralPELSpread.complexReferenceIso
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}
    {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : Base.ArithmeticBaseExtension K κ} (T : PEL.Has.IntegralPELSpread P iota κ N M U B) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj T.toOver ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (Reduction.reduction M) :=
  (Group.BaseChangeComparisons.GroupBaseChange.iteratedIso T.toOver B.generic (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))
    (Spec.map_comp (CommRingCat.ofHom B.toField) (CommRingCat.ofHom B.embedding)).symm).symm ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).mapIso T.genericIso ≪≫
      Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (Reduction.reduction M)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
