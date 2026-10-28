import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateFibers
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointField

/-! # Component Field Point -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The descended CM point carries its actual extension of the original
coefficient field and its actual point on the fixed integral component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K) (a : M.Family) (t : Fin (M.componentCount a))
  {F : Subfield ℂ} (p : Spec (.of F) ⟶ (M.embeddedGenericComponent a t).left)

def Models.RankThreePELModel.componentPointFieldEmbedding : M.arithmetic.extension.carrier →+* F :=
  (PointField.pointCoefficientEmbedding (M.embeddedGenericComponent a t) p).comp
    M.arithmetic.embedding.rangeRestrictField

def Models.RankThreePELModel.componentFieldPoint : Spec (.of F) ⟶ ((M.components a).S t).left :=
  p ≫ pullback.fst (M.genericComponent a t).hom
    (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField)) ≫
      pullback.fst ((M.components a).S t).hom M.arithmetic.generic

theorem Models.RankThreePELModel.componentPointFieldEmbedding_compatible
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t))
    (hp : Spec.map (CommRingCat.ofHom F.subtype) ≫ p = M.embeddedComponentPoint a t x) :
    F.subtype.comp (M.componentPointFieldEmbedding a t p) = M.arithmetic.embedding := by
  have hi := PointField.pointCoefficientEmbedding_compatible (M.embeddedGenericComponent a t) p
    M.arithmetic.embedding.fieldRange.subtype F.subtype (M.embeddedComponentPoint a t x)
    hp (M.embeddedComponentPoint_base a t x)
  change F.subtype.comp ((PointField.pointCoefficientEmbedding (M.embeddedGenericComponent a t) p).comp
    M.arithmetic.embedding.rangeRestrictField) = _
  rw [← RingHom.comp_assoc, hi]
  rfl

theorem Models.RankThreePELModel.componentFieldPoint_base :
    M.componentFieldPoint a t p ≫ ((M.components a).S t).hom =
      Spec.map (CommRingCat.ofHom (M.componentPointFieldEmbedding a t p)) ≫ M.arithmetic.generic := by
  dsimp only [Models.RankThreePELModel.componentFieldPoint]
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc]
  rw [← Category.assoc, Category.assoc p]
  change (p ≫ (pullback.fst (M.genericComponent a t).hom _ ≫ (M.genericComponent a t).hom)) ≫ _ = _
  rw [pullback.condition, ← Category.assoc p]
  change ((p ≫ (M.embeddedGenericComponent a t).hom) ≫ _) ≫ _ = _
  rw [← PointField.pointCoefficientEmbedding_spec, ← Spec.map_comp]
  rfl

theorem Models.RankThreePELModel.componentFieldPoint_complex
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t))
    (hp : Spec.map (CommRingCat.ofHom F.subtype) ≫ p = M.embeddedComponentPoint a t x) :
    Spec.map (CommRingCat.ofHom F.subtype) ≫ M.componentFieldPoint a t p =
      x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint := by
  dsimp only [Models.RankThreePELModel.componentFieldPoint]
  rw [← Category.assoc, hp, ← Category.assoc, Models.RankThreePELModel.embeddedComponentPoint_generic]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => x.left ≫ f)
      ((Category.assoc _ _ _).trans
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst ((M.components a).S t) M.arithmetic.generic
          (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))))))

theorem Models.RankThreePELModel.exists_coordinate_CM_arithmetic_component_point
    [IsGalois ℚ E]
    (hCMAbelianVariety : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) :
    ∃ (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) (F : Subfield ℂ),
      NumberField F ∧
      ∃ (i : M.arithmetic.extension.carrier →+* F)
        (p : Spec (.of F) ⟶ ((M.components a).S t).left),
        F.subtype.comp i = M.arithmetic.embedding ∧
        p ≫ ((M.components a).S t).hom = Spec.map (CommRingCat.ofHom i) ≫ M.arithmetic.generic ∧
        Spec.map (CommRingCat.ofHom F.subtype) ≫ p =
          x.left ≫ pullback.fst ((M.components a).S t).hom M.arithmetic.complexPoint ∧
        CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
          (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
            (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x)) := by
  obtain ⟨x, F, hF, hCM, p, hp⟩ :=
    M.exists_coordinate_CM_point_over_numberField_on_component hCMAbelianVariety hM a t
  exact ⟨x, F, hF, M.componentPointFieldEmbedding a t p, M.componentFieldPoint a t p,
    M.componentPointFieldEmbedding_compatible a t p x hp, M.componentFieldPoint_base a t p,
    M.componentFieldPoint_complex a t p x hp, hCM⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
