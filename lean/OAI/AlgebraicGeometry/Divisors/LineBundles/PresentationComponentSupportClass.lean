import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GeometricCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedOpenClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PointComponentDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology

/-! # Presentation Component Support Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentSupportClass.BundleCycles

noncomputable section

section

/-! Native geometry and exact dimension bookkeeping for the canonical class on an integral smooth projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

instance presentationOver_smooth : Smooth X.toOver.hom := X.smooth
instance presentationOver_noetherian : AlgebraicGeometry.IsNoetherian X.toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian X.carrier)
instance presentationOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) := by
  let : IsProper X.toOver.hom := X.projective.isProper
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable X.toOver
instance presentationOver_separated : IsSeparated X.toOver.hom :=
  inferInstanceAs (IsSeparated X.structureMap)
instance presentationComponentOver_open (C : irreducibleComponents X.carrier) :
    IsOpenImmersion (X.componentInclusionOver C).left := X.componentInclusion_isOpenImmersion C

variable [IsIntegral X.carrier]

instance presentationOver_integral : IsIntegral X.toOver.left := inferInstanceAs (IsIntegral X.carrier)

theorem integralPresentation_componentDimension (C : irreducibleComponents X.carrier) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap :=
  Open.SupportOver.BundleCycles.openImmersionOver_dimension (X.componentInclusionOver C)

theorem integralPresentation_components_equal (C D : irreducibleComponents X.carrier) : C = D := by
  apply Subtype.ext
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  have hD : D.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using D.property
  exact hC.trans hD.symm

theorem integralPresentationSupport_dimension (p : ℕ) (Z : X.DimensionCycleSupport p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.val X.structureMap + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  have h := Projective.PointComponentDimension.BundleCycles.projectiveSupport_dimension_add_codimension X Z.val
  rw [Z.property, integralPresentation_componentDimension X] at h
  exact h

end

/-! On an integral presentation, the canonical class of a component support image restricts to that support's independently defined geometric class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (p : ℕ) (C : irreducibleComponents X.carrier)
  (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p)

instance componentImageSupport_open_nonempty :
    Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback (X.componentInclusion C) (X.componentSupportImage C Z.val)) := by
  apply (Open.SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff _ _).mpr
  obtain ⟨x, hx⟩ := Z.val.isIrreducible.nonempty
  exact ⟨x, ⟨x, hx, rfl⟩⟩

omit [AlgebraicGeometry.IsIntegral X.carrier] in
theorem componentImageSupport_openRestriction :
    Open.SupportRestriction.BundleCycles.openRestrictedSupport (X.componentInclusion C) (X.componentSupportImage C Z.val) = Z.val := by
  apply IrreducibleCloseds.ext
  rw [Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe, X.componentSupportImage_coe]
  exact Set.preimage_image_eq _ (X.componentInclusion C).isOpenEmbedding.injective

include p in
theorem componentImageSupport_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (X.componentSupportImage C Z.val) X.structureMap + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap :=
  (congrArg (fun n => n + p) (X.componentSupportImage_transcendenceDimension C Z.val)).trans
    (Z.dimension_add_codimension.trans (integralPresentation_componentDimension X C))

theorem componentImageSupport_cycleClass :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X.toOver (X.componentSupportImage C Z.val) p (componentImageSupport_codimension X p C Z)) =
      Z.geometricCycleClass := by
  let : Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback (X.componentInclusionOver C).left (X.componentSupportImage C Z.val)) :=
    componentImageSupport_open_nonempty X p C Z
  have h := Scheme.AbsoluteOpenPullback.BundleCycles.schemeCycleClass_openPullback (X.componentInclusionOver C) (X.componentSupportImage C Z.val) p
    (componentImageSupport_codimension X p C Z)
  exact h.trans ((Scheme.GradedAbsoluteClass.BundleCycles.schemeCycleClass_congrSupport (X.componentVariety C).toOver _ _
    (componentImageSupport_openRestriction X p C Z) p _ _).trans
      (Scheme.GeometricCycleClass.BundleCycles.schemeCycleClass_geometric (X.componentVariety C) p Z))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentSupportClass.BundleCycles
