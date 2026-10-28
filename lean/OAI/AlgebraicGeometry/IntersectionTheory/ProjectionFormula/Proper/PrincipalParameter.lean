import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.IntegralImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.DivisorNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PrincipalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Principal Parameter -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalParameter

noncomputable section

/-! Principal divisors on arbitrary proper integral parameter schemes
produce native ambient rational-equivalence relations. The source can be
singular and need not itself have a smooth presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Z : Scheme} [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Z] (f : Z ⟶ X.carrier) [IsProper f]

omit [AlgebraicGeometry.IsNoetherian Z] in
theorem factor (c : Z →₀ ℚ) : CyclePushforward.pointPushforward f c =
    CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure f))
      (CyclePushforward.pointPushforward (IntegralImage.map X f) c) := by
  rw [← LinearMap.comp_apply, ← CyclePushforward.pointPushforward_comp, IntegralImage.map_fac]

theorem norm (p : ℕ)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap))
    (g : Z.functionField) (hg : g ≠ 0) :
    ∃ h : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure f)).functionField, h ≠ 0 ∧
      CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor Z g)) =
        Principal.ClosedSectionCycle.principalCycle X p (CycleClass.Geometric.StratumClosure.integralImageClosure f) h := by
  let W := CycleClass.Geometric.StratumClosure.integralImageClosure f
  let φ := IntegralImage.map X f
  let hη := IntegralImage.map_genericPoint X f
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap φ hη).hom.toAlgebra
  let := IntegralImage.field_finite X f hd
  let h := Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField g
  refine ⟨h, Algebra.norm_ne_zero_iff.mpr hg, ?_⟩
  have he := DivisorNorm.principalDivisor_norm φ hη (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap)
    (IntegralImage.field_finite X f hd) g hg
  rw [factor X f, he]
  exact (Principal.ClosedSectionCycle.principalCycle_eq_pushforward X p W h).symm

theorem drop_one
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap))
    (g : Z.functionField) (hg : g ≠ 0) : CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor Z g) = 0 := by
  let W := CycleClass.Geometric.StratumClosure.integralImageClosure f
  let φ := IntegralImage.map X f
  let : IsProper X.structureMap := X.projective.isProper
  let : Foundations.Scheme.ProjectiveSpace.complexBase.IsSeparated := by
    change (Spec (.of ℂ)).IsSeparated
    infer_instance
  let : Z.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (f ≫ X.structureMap)]
    infer_instance⟩
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap)]
    dsimp only [CycleClass.Geometric.SupportFiniteType.supportStructureMap]
    infer_instance⟩
  have hd' : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (φ ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) := by
    rw [IntegralImage.map_over]
    exact hd
  have he := Relative.PrincipalDivisor.pushforward_eq_zero φ
    (IntegralImage.map_genericPoint X f) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap) hd' g hg
  rw [factor X f, he, map_zero]

omit [AlgebraicGeometry.IsNoetherian Z] [IsProper f] in
theorem degree_zero (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap + p < m)
    (c : Z →₀ ℚ) : CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f c) = 0 := by
  apply Finsupp.ext
  intro C
  rw [Principal.ClosedSectionCycle.degreeComponent_apply, Finsupp.zero_apply]
  apply PushforwardFiber.pointPushforward_apply_eq_zero
  intro z _ he
  have hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (CycleClass.Geometric.StratumClosure.integralImageClosure f : Set X.carrier) :=
    Set.mem_of_eq_of_mem he.symm (subset_closure (show f z ∈ Set.range f from ⟨z, rfl⟩))
  have hCW : C.val ≤ CycleClass.Geometric.StratumClosure.integralImageClosure f := (Supports.supportPoint_mem_iff_subset
    (⟨(CycleClass.Geometric.StratumClosure.integralImageClosure f : Set X.carrier), (CycleClass.Geometric.StratumClosure.integralImageClosure f).isClosed⟩ : Closeds X.carrier) C.val).mp hxW
  have hle := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap).monotone hCW
  have hdim := Grading.supportDimension_add_codimension X m C.val
  rw [C.property] at hdim
  omega

theorem relation (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (g : Z.functionField) (hg : g ≠ 0) :
    CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor Z g)) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p := by
  have hle := IntegralImage.dimension_le X f
  by_cases heq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap)
  · obtain ⟨h, hh, he⟩ := PrincipalParameter.norm X f p heq g hg
    rw [he]
    apply Submodule.subset_span
    apply Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X p (CycleClass.Geometric.StratumClosure.integralImageClosure f) _ h hh
    have hdim := Grading.supportDimension_add_codimension X m (CycleClass.Geometric.StratumClosure.integralImageClosure f)
    omega
  by_cases hone : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Geometric.StratumClosure.integralImageClosure f) X.structureMap + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap)
  · rw [drop_one X f hone g hg, map_zero]
    exact Submodule.zero_mem _
  · rw [degree_zero X f m p (by omega)]
    exact Submodule.zero_mem _

theorem zeros_poles (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1)
    (g : Z.functionField) (hg : g ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g))))
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g⁻¹)))) := by
  have h := relation X f m p hd g hg
  rw [PositiveCycle.principalDivisor_eq_positive_sub_inverse g, map_sub, map_sub] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalParameter
