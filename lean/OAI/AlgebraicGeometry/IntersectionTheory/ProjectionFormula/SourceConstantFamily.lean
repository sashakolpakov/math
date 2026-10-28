import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactHorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductSupportDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

/-! # Source Constant Family -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantFamily

noncomputable section

section

/-! The intrinsic moving source family is smooth of dimension m+1,
and integral when the source is integral. Its native stalks therefore
carry the finite projective-dimension bound used in fiber comparisons. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FamilyRegularity

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

def base : Projective.FamilyOnSource.Family.space X A ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap

theorem parameter_base : Projective.FamilySections.Family.parameter X A ≫
    Parameter.Polynomial.IntegralProduct.parameterBase A = base X A :=
  (Projective.FamilyIs.FamilyFibers.source_base_change X A).w.symm

theorem relativeDimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    SmoothOfRelativeDimension m (Projective.FamilySections.Family.parameter X A) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension m) :=
    smoothOfRelativeDimension_isStableUnderBaseChange m
  exact MorphismProperty.of_isPullback (Projective.FamilyIs.FamilyFibers.source_base_change X A)
    (inferInstanceAs (SmoothOfRelativeDimension m X.structureMap))

theorem totalDimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    SmoothOfRelativeDimension (m + 1) (base X A) := by
  let := relativeDimension X A m
  rw [← parameter_base]
  exact smoothOfRelativeDimension_comp (Projective.FamilySections.Family.parameter X A)
    (Parameter.Polynomial.IntegralProduct.parameterBase A) (n := m) (m := 1)

theorem integral [IsIntegral X.carrier] : IsIntegral (Projective.FamilyOnSource.Family.space X A) :=
  inferInstanceAs (IsIntegral (Parameter.Polynomial.ProjectiveSubschemeFamily.space A X.embedding))

theorem stalk_bound (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (x : Projective.FamilyOnSource.Family.space X A) :
    Polynomial.DimensionBound.GlobalBound ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk x) (m + 1) := by
  let := totalDimension X A m
  exact ProjectionFormula.Smooth.StalkDimension.stalk_bound (base X A) (m + 1) x

end FamilyRegularity

end

section

/-! A fixed integral support of X has its actual constant closed
family inside the intrinsic moving source family. Its support is the
inverse image of the fixed support and it is flat over the parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (B : IrreducibleCloseds X.carrier)

abbrev embedding : CycleClass.Geometric.GenericPoint.reducedSupportScheme B ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension :=
  CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ X.embedding

abbrev space : Scheme := Parameter.Polynomial.ProjectiveSubschemeFamily.space A (Family.embedding X B)

def map : space X A B ⟶ Projective.FamilyOnSource.Family.space X A :=
  pullback.map _ _ _ _ (𝟙 _) (CycleClass.Geometric.GenericPoint.reducedSupportι B) (𝟙 _)
    (by simp) (by simp [Family.embedding])

instance closed : IsClosedImmersion (Family.map X A B) := by
  unfold Family.map
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (𝟙 (Projective.MatrixFamily.Family.space A))))
    (inferInstanceAs (IsClosedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι B))) (by simp) (by simp [Family.embedding])

theorem toAmbient : Family.map X A B ≫ Projective.FamilyOnSource.Family.toAmbient X A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A (Family.embedding X B) := by
  simp [Family.map, Projective.FamilyOnSource.Family.toAmbient, Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient]

theorem toSource : Family.map X A B ≫ Projective.FamilyOnSource.Family.toSource X A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A (Family.embedding X B) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B := by
  simp [Family.map, Projective.FamilyOnSource.Family.toSource, Parameter.Polynomial.ProjectiveSubschemeFamily.toSource]

theorem isPullback : IsPullback (Family.map X A B) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A (Family.embedding X B))
    (Projective.FamilyOnSource.Family.toSource X A) (CycleClass.Geometric.GenericPoint.reducedSupportι B) := by
  apply (IsPullback.paste_horiz_iff
    (IsPullback.of_hasPullback (Projective.FamilySupport.Family.projection A) X.embedding) (toSource X A B)).mp
  change IsPullback (Family.map X A B ≫ Projective.FamilyOnSource.Family.toAmbient X A)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A (Family.embedding X B))
    (Projective.FamilySupport.Family.projection A) (Family.embedding X B)
  rw [toAmbient]
  exact IsPullback.of_hasPullback (Projective.FamilySupport.Family.projection A) (Family.embedding X B)

theorem parameter : Family.map X A B ≫ Projective.FamilySections.Family.parameter X A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A (Family.embedding X B) := by
  change Family.map X A B ≫ (Projective.FamilyOnSource.Family.toAmbient X A ≫ _) = _
  rw [← Category.assoc, toAmbient]
  rfl

theorem parameterLine : Family.map X A B ≫ CompactHorizontalFamilyFiber.Family.parameter X A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A (Family.embedding X B) ≫ Parameter.Polynomial.IntegralProduct.toLine A := by
  change Family.map X A B ≫ (Projective.FamilySections.Family.parameter X A ≫ _) = _
  rw [← Category.assoc, parameter]

def support : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A) :=
  Closed.ImmersionSupport.support (Family.map X A B)

theorem support_coe : (support X A B : Set (Projective.FamilyOnSource.Family.space X A)) =
    Projective.FamilyOnSource.Family.toSource X A ⁻¹' (B : Set X.carrier) := by
  rw [support, ProjectionFormula.Flat.ClosedSupport.support_range]
  rw [Open.SupportClosure.Pullback.range (Family.map X A B) (Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A (Family.embedding X B))
    (Projective.FamilyOnSource.Family.toSource X A) (CycleClass.Geometric.GenericPoint.reducedSupportι B) (isPullback X A B), CycleClass.Geometric.GenericPoint.range_reducedSupportι]

instance flat_parameter : Flat (Family.map X A B ≫ CompactHorizontalFamilyFiber.Family.parameter X A) := by
  rw [parameterLine]
  infer_instance

instance support_flat : Flat (CycleClass.Geometric.GenericPoint.reducedSupportι (support X A B) ≫ CompactHorizontalFamilyFiber.Family.parameter X A) :=
  ProjectionFormula.Flat.ClosedSupport.flat (Family.map X A B) (CompactHorizontalFamilyFiber.Family.parameter X A)

theorem section_square (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A (Family.embedding X B) a ha ≫ Family.map X A B =
      CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ Projective.FamilyOnSource.Family.specialization X A a ha := by
  apply pullback.hom_ext
  · change (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A (Family.embedding X B) a ha ≫ Family.map X A B) ≫
        Projective.FamilyOnSource.Family.toAmbient X A =
      (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ Projective.FamilyOnSource.Family.specialization X A a ha) ≫
        Projective.FamilyOnSource.Family.toAmbient X A
    simp only [Category.assoc, toAmbient, Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_ambient,
      Projective.FamilyOnSource.Family.specialization_ambient]
  · change (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A (Family.embedding X B) a ha ≫ Family.map X A B) ≫
        Projective.FamilyOnSource.Family.toSource X A =
      (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ Projective.FamilyOnSource.Family.specialization X A a ha) ≫
        Projective.FamilyOnSource.Family.toSource X A
    rw [Category.assoc, toSource, ← Category.assoc,
      Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_source, Category.id_comp,
      Category.assoc, Projective.FamilyOnSource.Family.specialization_source, Category.comp_id]

end Family

end

/-! The constant source family of a support has dimension at most
the support dimension plus the one parameter dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Dimension

theorem bound (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
    (B : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Family.support X A B)
      (FamilyRegularity.base X A) ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap + 1 := by
  let i := Family.embedding X B
  let f := Parameter.Polynomial.IntegralProduct.parameterBase A
  let g := i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension
  let e := Parameter.Polynomial.ProjectiveSubschemeFamily.productIso A i
  let J := Family.map X A B
  let : Nonempty (Spec (.of (Polynomial.MatrixPath.Ring A))) :=
    ⟨(Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A 0
      (Polynomial.MatrixPath.zero_good A)))) (IsLocalRing.closedPoint ℂ)⟩
  let : IsIntegral (Spec (.of (Polynomial.MatrixPath.Ring A))) :=
    isIntegral_of_isOpenImmersion (Parameter.Polynomial.IntegralProduct.toLine A)
  have hg : g = CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ X.structureMap := by
    change (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ X.embedding) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension = _
    rw [Category.assoc, X.embedding_over]
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : LocallyOfFiniteType g := by rw [hg]; infer_instance
  have hgd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap := by
    rw [hg]
    rfl
  have he : e.hom ≫ pullback.fst f g ≫ f =
      Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i ≫ g := by
    have he₁ : e.hom ≫ pullback.fst f g = Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i :=
      (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i).isoPullback_hom_fst
    rw [← Category.assoc, he₁]
    exact (Parameter.Polynomial.ProjectiveSubschemeFamily.base_change A i).w
  have hJ : J ≫ FamilyRegularity.base X A =
      Parameter.Polynomial.ProjectiveSubschemeFamily.toSource A i ≫ g := by
    change J ≫ (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) = _
    rw [← Category.assoc, Family.toSource, Category.assoc, ← hg]
  have himage := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure J (FamilyRegularity.base X A)
  have heimage := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure e.hom (pullback.fst f g ≫ f)
  have hb := ProductSupportDimension.bound f g (CycleClass.Geometric.StratumClosure.integralImageClosure e.hom)
  have hf : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = 1 :=
    Grading.integral_dimension_of_relativeDimension f 1
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure J) (FamilyRegularity.base X A) ≤ _
  rw [← himage, hJ, ← he, heimage]
  rw [hf, hgd] at hb
  simpa only [Nat.add_comm] using hb

end Dimension

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantFamily
