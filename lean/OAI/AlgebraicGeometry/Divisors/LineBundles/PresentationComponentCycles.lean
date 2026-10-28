import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PresentationCycleComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionSet

/-! # Presentation Component Cycles -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentCycles.Bundle

noncomputable section

section

/-! Actual component restriction of presentation cycles preserves each generic-point coefficient and its codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)

theorem componentPresentation_pointCodimension (x : (X.componentVariety C).carrier) :
    X.supportCodimension (irreducibleSetEquivPoints.symm (X.componentInclusion C x)) =
      (X.componentVariety C).presentation.supportCodimension (irreducibleSetEquivPoints.symm x) := by
  have hs : X.componentSupportImage C (irreducibleSetEquivPoints.symm x) =
      irreducibleSetEquivPoints.symm (X.componentInclusion C x) := by
    apply irreducibleSetEquivPoints.injective
    rw [X.componentSupportImage_genericPoint, irreducibleSetEquivPoints.apply_symm_apply,
      irreducibleSetEquivPoints.apply_symm_apply]
  exact (congrArg X.supportCodimension hs).symm.trans
    ((X.supportCodimension_componentSupportImage C _).trans
      (Integral.PresentationCycleComparison.BundleCycles.integralPresentation_supportCodimension (X.componentVariety C) _).symm)

def presentationComponentSupportEmbedding (p : ℕ) :
    (X.componentVariety C).presentation.DimensionCycleSupport p ↪ X.DimensionCycleSupport p where
  toFun Z := ⟨X.componentSupportImage C Z.val,
    (X.supportCodimension_componentSupportImage C Z.val).trans
      ((Integral.PresentationCycleComparison.BundleCycles.integralPresentation_supportCodimension (X.componentVariety C) Z.val).symm.trans Z.property)⟩
  inj' := fun _ _ h => Subtype.ext (X.componentSupportImage_injective C (congrArg Subtype.val h))

def presentationComponentCycle (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] (X.componentVariety C).presentation.RationalDimensionCycle p :=
  Finsupp.lcomapDomain (presentationComponentSupportEmbedding X C p) (presentationComponentSupportEmbedding X C p).injective

theorem presentationComponentSupportEmbedding_point (p : ℕ)
    (Z : (X.componentVariety C).presentation.DimensionCycleSupport p) :
    Chow.BundleCycles.cyclePointEmbedding X p (presentationComponentSupportEmbedding X C p Z) =
      X.componentInclusion C (Chow.BundleCycles.cyclePointEmbedding (X.componentVariety C).presentation p Z) :=
  X.componentSupportImage_genericPoint C Z.val

theorem presentationComponentCycle_forget (p : ℕ) (z : X.RationalDimensionCycle p) :
    Chow.BundleCycles.pointCycle (X.componentVariety C).presentation p (presentationComponentCycle X C p z) =
      Finsupp.comapDomain (X.componentInclusion C) (Chow.BundleCycles.pointCycle X p z)
        (X.componentInclusion C).isOpenEmbedding.injective.injOn := by
  ext x
  by_cases hx : x ∈ Set.range (Chow.BundleCycles.cyclePointEmbedding (X.componentVariety C).presentation p)
  · obtain ⟨Z, rfl⟩ := hx
    exact (Chow.BundleCycles.pointCycle_apply (X.componentVariety C).presentation p (presentationComponentCycle X C p z) Z).trans
      ((Chow.BundleCycles.pointCycle_apply X p z (presentationComponentSupportEmbedding X C p Z)).symm.trans
        (congrArg (Chow.BundleCycles.pointCycle X p z) (presentationComponentSupportEmbedding_point X C p Z)))
  · have hn : (X.componentVariety C).presentation.supportCodimension (irreducibleSetEquivPoints.symm x) ≠ p := by
      intro he
      exact hx ⟨⟨irreducibleSetEquivPoints.symm x, he⟩, irreducibleSetEquivPoints.apply_symm_apply x⟩
    have hi : X.componentInclusion C x ∉ Set.range (Chow.BundleCycles.cyclePointEmbedding X p) := by
      intro hm
      have hc := (congrArg (fun S => X.componentInclusion C x ∈ S) (Projective.CodimensionSet.BundleCycles.cyclePointEmbedding_range X p)).mp hm
      exact hn ((componentPresentation_pointCodimension X C x).symm.trans hc)
    exact (Finsupp.embDomain_of_notMem_range _ _ x hx).trans
      (Finsupp.embDomain_of_notMem_range _ _ (X.componentInclusion C x) hi).symm

theorem presentationComponentCycle_native (p : ℕ) (z : X.RationalDimensionCycle p) :
    presentationComponentCycle X C p z =
      Integral.PresentationCycleComparison.BundleCycles.integralVarietyPresentationCycle (X.componentVariety C) p (X.componentDimensionCycleEquiv p z C) := by
  ext Z
  let W : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p :=
    ⟨Z.val, (Integral.PresentationCycleComparison.BundleCycles.integralPresentation_supportCodimension (X.componentVariety C) Z.val).symm.trans Z.property⟩
  have he : Integral.PresentationCycleComparison.BundleCycles.integralVarietyPresentationSupport (X.componentVariety C) p W = Z := Subtype.ext rfl
  have hinj : Function.Injective (Integral.PresentationCycleComparison.BundleCycles.integralVarietyPresentationSupport (X.componentVariety C) p) :=
    fun _ _ h => Subtype.ext (congrArg (fun Q : (X.componentVariety C).presentation.DimensionCycleSupport p => Q.val) h)
  have hc := Finsupp.mapDomain_apply_of_injective hinj (X.componentDimensionCycleEquiv p z C) W
  exact hc.symm.trans (congrArg (fun Q => Integral.PresentationCycleComparison.BundleCycles.integralVarietyPresentationCycle (X.componentVariety C) p
    (X.componentDimensionCycleEquiv p z C) Q) he)

theorem presentationComponentCycle_class (p : ℕ) (z : X.RationalDimensionCycle p) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C) (X.geometricCycleClassMap p z) =
      (X.componentVariety C).presentation.geometricCycleClassMap p (presentationComponentCycle X C p z) := by
  have hc := (X.componentBettiEquiv_apply (ModuleCat.of ℚ ℚ) (p + p) (X.geometricCycleClassMap p z) C).symm.trans
    (X.componentBettiEquiv_geometricCycleClassMap p z C)
  exact hc.trans ((Integral.PresentationCycleComparison.BundleCycles.integralVarietyPresentationCycle_class (X.componentVariety C) p _).symm.trans
    (congrArg ((X.componentVariety C).presentation.geometricCycleClassMap p)
      (presentationComponentCycle_native X C p z).symm))

end

/-! Component restriction preserves the chosen codimension of every point cycle and its independently constructed geometric Chow class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) (p : ℕ)

theorem presentationComponentCycle_codimensionPart (z : X.carrier →₀ ℚ) :
    presentationComponentCycle X C p (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p z) =
      Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent (X.componentVariety C).presentation p
        (Finsupp.comapDomain (X.componentInclusion C) z (X.componentInclusion C).isOpenEmbedding.injective.injOn) := by
  apply Chow.BundleCycles.pointCycle_injective (X.componentVariety C).presentation p
  rw [presentationComponentCycle_forget, Projective.CodimensionSet.BundleCycles.pointCycle_projectiveCodimensionComponent,
    Projective.CodimensionSet.BundleCycles.pointCycle_projectiveCodimensionComponent]
  ext x
  change Point.CycleSet.BundleCycles.pointCycleSetPart {y | X.supportCodimension (irreducibleSetEquivPoints.symm y) = p} z
      (X.componentInclusion C x) = _
  by_cases hx : (X.componentVariety C).presentation.supportCodimension (irreducibleSetEquivPoints.symm x) = p
  · have hi := (componentPresentation_pointCodimension X C x).trans hx
    exact (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem
      {y | X.supportCodimension (irreducibleSetEquivPoints.symm y) = p} z (X.componentInclusion C x) hi).trans
      (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem
        {y | (X.componentVariety C).presentation.supportCodimension (irreducibleSetEquivPoints.symm y) = p}
        (Finsupp.comapDomain (X.componentInclusion C) z (X.componentInclusion C).isOpenEmbedding.injective.injOn) x hx).symm
  · have hi : X.supportCodimension (irreducibleSetEquivPoints.symm (X.componentInclusion C x)) ≠ p :=
      fun he => hx ((componentPresentation_pointCodimension X C x).symm.trans he)
    exact (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem
      {y | X.supportCodimension (irreducibleSetEquivPoints.symm y) = p} z (X.componentInclusion C x) hi).trans
      (Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem
        {y | (X.componentVariety C).presentation.supportCodimension (irreducibleSetEquivPoints.symm y) = p}
        (Finsupp.comapDomain (X.componentInclusion C) z (X.componentInclusion C).isOpenEmbedding.injective.injOn) x hx).symm

theorem geometricCycleClassQ_component_pointClass (z : X.carrier →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C)
      (Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p (Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p z)) =
      Geometric.CycleClass.BundleCycles.geometricCycleClassQ (X.componentVariety C).presentation p
        (Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass (X.componentVariety C).presentation p
          (Finsupp.comapDomain (X.componentInclusion C) z (X.componentInclusion C).isOpenEmbedding.injective.injOn)) := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C)
    (X.geometricCycleClassMap p (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p z)) =
    (X.componentVariety C).presentation.geometricCycleClassMap p
      (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent (X.componentVariety C).presentation p
        (Finsupp.comapDomain (X.componentInclusion C) z (X.componentInclusion C).isOpenEmbedding.injective.injOn))
  exact (presentationComponentCycle_class X C p (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p z)).trans
    (congrArg ((X.componentVariety C).presentation.geometricCycleClassMap p)
      (presentationComponentCycle_codimensionPart X C p z))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentCycles.Bundle
