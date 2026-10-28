import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionComplex
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison

/-! # Integral Complex Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The complex point space of the supplied integral model is identified
with the original fine PEL point space through its literal generic iso. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

abbrev Models.RankThreePELModel.integralComplexModuli (a : M.Family) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  (Over.pullback M.arithmetic.complexPoint).obj (M.integral a).toOver

def Models.RankThreePELModel.integralComplexReductionIso (a : M.Family) :
    M.integralComplexModuli a ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom M.complexEmbedding))).obj
        (IntegralModel.Reduction.reduction (M.moduli a).space) :=
  (Over.pullbackComp (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))
    M.arithmetic.generic).app (M.integral a).toOver ≪≫
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))).mapIso
    (M.integral a).genericIso ≪≫
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso M.arithmetic (IntegralModel.Reduction.reduction (M.moduli a).space)

def Models.RankThreePELModel.integralComplexFinePELMap (a : M.Family) :
    M.integralComplexModuli a ⟶ (M.moduli a).complexFiber M.complexEmbedding :=
  (M.integralComplexReductionIso a).hom ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom M.complexEmbedding))).map
      (IntegralModel.Reduction.reductionι (M.moduli a).space)

def Models.RankThreePELModel.integralComplexFinePELHomeomorph (a : M.Family) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexModuli a) ≃ₜ
      (M.moduli a).ComplexPoints M.complexEmbedding :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (M.integralComplexReductionIso a)).trans
    (ReductionComplex.reductionComplexPointHomeomorph (M.moduli a).space
      (Spec.map (CommRingCat.ofHom M.complexEmbedding)))

theorem Models.RankThreePELModel.integralComplexFinePELHomeomorph_apply (a : M.Family)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexModuli a)) :
    M.integralComplexFinePELHomeomorph a x =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexFinePELMap a) x := by
  change (x ≫ (M.integralComplexReductionIso a).hom) ≫ _ = x ≫ _
  exact Category.assoc _ _ _

instance Models.RankThreePELModel.integralComponentInclusion_closed (a : M.Family) (t : Fin (M.componentCount a)) :
    IsClosedImmersion (M.integralComponentInclusion a t).left := by
  let : IsOpenImmersion (M.integralComponentInclusion a t).left :=
    IntegralModel.Coproduct.decomposition_inclusion_open (M.components a).S (M.decomposition a) t
  apply IsClosedImmersion.of_isPreimmersion
  let e := IntegralModel.Coproduct.decompositionHomeomorph (M.components a).S (M.decomposition a)
  have hr : Set.range (M.integralComponentInclusion a t).left =
      e '' Set.range (Sigma.mk t) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    exact (IntegralModel.Coproduct.decompositionHomeomorph_apply (M.components a).S (M.decomposition a) t x).symm
  rw [hr]
  exact e.isClosedMap _ isClosed_range_sigmaMk

abbrev Models.RankThreePELModel.integralComplexComponent (a : M.Family) (t : Fin (M.componentCount a)) :
    Over Foundations.Scheme.ProjectiveSpace.complexBase := (Over.pullback M.arithmetic.complexPoint).obj ((M.components a).S t)

def Models.RankThreePELModel.integralComplexComponentInclusion (a : M.Family) (t : Fin (M.componentCount a)) :
    M.integralComplexComponent a t ⟶ M.integralComplexModuli a :=
  (Over.pullback M.arithmetic.complexPoint).map (M.integralComponentInclusion a t)

instance Models.RankThreePELModel.integralComplexComponentInclusion_closed (a : M.Family) (t : Fin (M.componentCount a)) :
    IsClosedImmersion (M.integralComplexComponentInclusion a t).left :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion) _ _ inferInstance

instance Models.RankThreePELModel.integralComplexComponentInclusion_open (a : M.Family) (t : Fin (M.componentCount a)) :
    IsOpenImmersion (M.integralComplexComponentInclusion a t).left := by
  let : IsOpenImmersion (M.integralComponentInclusion a t).left :=
    IntegralModel.Coproduct.decomposition_inclusion_open (M.components a).S (M.decomposition a) t
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _ inferInstance

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
