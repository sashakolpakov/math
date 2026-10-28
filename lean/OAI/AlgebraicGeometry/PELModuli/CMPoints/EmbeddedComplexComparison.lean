import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComplexComparison

/-! # Embedded Complex Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The exact field-range and generic-fiber comparisons for complex
points of arithmetic schemes. All maps retain their pullback projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def EmbeddedComplexComparison.fieldRangeComplexIso {F : Type} [Field F] (κ : F →+* ℂ)
    (X : Over (Spec (.of F))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom κ.fieldRange.subtype))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom κ.rangeRestrictField))).obj X) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X
    (Spec.map (CommRingCat.ofHom κ.rangeRestrictField))
    (Spec.map (CommRingCat.ofHom κ.fieldRange.subtype))
    (Spec.map (CommRingCat.ofHom κ)) (by rw [← Spec.map_comp]; rfl)

theorem EmbeddedComplexComparison.fieldRangeComplexIso_fst {F : Type} [Field F] (κ : F →+* ℂ)
    (X : Over (Spec (.of F))) :
    (EmbeddedComplexComparison.fieldRangeComplexIso κ X).hom.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom κ)) =
    pullback.fst ((Over.pullback (Spec.map (CommRingCat.ofHom κ.rangeRestrictField))).obj X).hom
      (Spec.map (CommRingCat.ofHom κ.fieldRange.subtype)) ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom κ.rangeRestrictField)) :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X _ _ _ _

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

abbrev Models.RankThreePELModel.embeddedComponentComplex (a : M.Family) (t : Fin (M.componentCount a)) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  (Over.pullback (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.fieldRange.subtype))).obj
    (M.embeddedGenericComponent a t)

def Models.RankThreePELModel.embeddedComponentComplexIso (a : M.Family) (t : Fin (M.componentCount a)) :
    M.embeddedComponentComplex a t ≅ M.integralComplexComponent a t :=
  EmbeddedComplexComparison.fieldRangeComplexIso M.arithmetic.embedding (M.genericComponent a t) ≪≫
    ((Over.pullbackComp (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))
      M.arithmetic.generic).app ((M.components a).S t)).symm

def Models.RankThreePELModel.embeddedComponentPoint (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    Foundations.Scheme.ProjectiveSpace.complexBase ⟶ (M.embeddedGenericComponent a t).left :=
  (x ≫ (M.embeddedComponentComplexIso a t).inv).left ≫
    pullback.fst (M.embeddedGenericComponent a t).hom
      (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.fieldRange.subtype))

theorem Models.RankThreePELModel.embeddedComponentPoint_base (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    M.embeddedComponentPoint a t x ≫ (M.embeddedGenericComponent a t).hom =
      Spec.map (CommRingCat.ofHom M.arithmetic.embedding.fieldRange.subtype) := by
  let y := x ≫ (M.embeddedComponentComplexIso a t).inv
  have hy : y.left ≫ pullback.snd (M.embeddedGenericComponent a t).hom
      (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.fieldRange.subtype)) = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := y.w
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => y.left ≫ k) (pullback.condition)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ Spec.map
          (CommRingCat.ofHom M.arithmetic.embedding.fieldRange.subtype)) hy).trans
            (Category.id_comp _))))

theorem Models.RankThreePELModel.embeddedComponentPoint_generic (a : M.Family) (t : Fin (M.componentCount a))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) :
    M.embeddedComponentPoint a t x ≫
      pullback.fst (M.genericComponent a t).hom
        (Spec.map (CommRingCat.ofHom M.arithmetic.embedding.rangeRestrictField)) =
    (x ≫ ((Over.pullbackComp (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))
      M.arithmetic.generic).app ((M.components a).S t)).hom).left ≫
      pullback.fst (M.genericComponent a t).hom
        (Spec.map (CommRingCat.ofHom M.arithmetic.embedding)) := by
  let u := (Over.pullbackComp (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))
    M.arithmetic.generic).app ((M.components a).S t)
  let v := EmbeddedComplexComparison.fieldRangeComplexIso M.arithmetic.embedding (M.genericComponent a t)
  let y := x ≫ (M.embeddedComponentComplexIso a t).inv
  have hy : y ≫ v.hom = x ≫ u.hom := by
    change (x ≫ (u.hom ≫ v.inv)) ≫ v.hom = x ≫ u.hom
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k => x ≫ k) ((Category.assoc _ _ _).trans
        ((congrArg (fun k => u.hom ≫ k) v.inv_hom_id).trans (Category.comp_id _))))
  have hv := EmbeddedComplexComparison.fieldRangeComplexIso_fst M.arithmetic.embedding (M.genericComponent a t)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => y.left ≫ k) hv.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f.left ≫ pullback.fst (M.genericComponent a t).hom
          (Spec.map (CommRingCat.ofHom M.arithmetic.embedding))) hy)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
