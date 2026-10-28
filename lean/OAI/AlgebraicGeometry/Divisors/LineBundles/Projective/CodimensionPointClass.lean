import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.TopDimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction

/-! # Codimension Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionPointClass.BundleCycles

noncomputable section

section

/-! The full principal divisor of an integral support lies in the
next codimension, measured in its actual smooth projective component. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem projectiveSupport_dimension_le_component (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent W)).structureMap := by
  let C := X.supportComponent W
  let V := X.componentSupportPreimage C W (X.support_subset_component W)
  have hd := TopDimensionChow.BundleCycles.integralSupport_dimension_le (X.componentVariety C).structureMap V
  have he := X.componentSupportImage_transcendenceDimension C V
  rw [X.componentSupportImage_preimage] at he
  exact he.trans_le hd

theorem projectiveSupportComponent_eq_of_le (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (Z W : IrreducibleCloseds X.carrier) (hZW : Z ≤ W) : X.supportComponent Z = X.supportComponent W :=
  X.supportComponent_eq_of_subset Z (X.supportComponent W)
    ((show (Z : Set X.carrier) ⊆ W from hZW).trans (X.support_subset_component W))

theorem schemePrincipalPointDivisor_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (x : X.carrier) (hx : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g x ≠ 0) :
    X.supportCodimension (irreducibleSetEquivPoints.symm x) = X.supportCodimension W + 1 := by
  have hxW : x ∈ (W : Set X.carrier) := by
    by_contra hn
    exact hx (Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support W g x hn)
  have hle : irreducibleSetEquivPoints.symm x ≤ W :=
    closure_minimal (Set.singleton_subset_iff.mpr hxW) W.isClosed
  have hC := projectiveSupportComponent_eq_of_le X _ W hle
  have hd := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension X.structureMap W g x hx
  have hbound := projectiveSupport_dimension_le_component X W
  have hN := congrArg (fun C : irreducibleComponents X.carrier =>
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety C).structureMap) hC
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension
  omega

end

/-! Taking a point cycle's codimension component defines its actual
projective Chow class and kills every geometric principal divisor. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)

def projectiveCodimensionComponent : (X.carrier →₀ ℚ) →ₗ[ℚ] X.RationalDimensionCycle p :=
  Finsupp.lcomapDomain (Chow.BundleCycles.cyclePointEmbedding X p) (Chow.BundleCycles.cyclePointEmbedding X p).injective

theorem projectiveCodimensionComponent_pointCycle (z : X.RationalDimensionCycle p) :
    projectiveCodimensionComponent X p (Chow.BundleCycles.pointCycle X p z) = z := by
  ext Z
  exact Chow.BundleCycles.pointCycle_apply X p z Z

theorem pointCycle_codimensionComponent_supported (z : X.carrier →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → X.supportCodimension (irreducibleSetEquivPoints.symm x) = p) :
    Chow.BundleCycles.pointCycle X p (projectiveCodimensionComponent X p z) = z := by
  have hs : (z.support : Set X.carrier) ⊆ Set.range (Chow.BundleCycles.cyclePointEmbedding X p) := by
    intro x hx
    exact ⟨⟨irreducibleSetEquivPoints.symm x, hz x (Finsupp.mem_support_iff.mp hx)⟩,
      irreducibleSetEquivPoints.apply_symm_apply x⟩
  exact Finsupp.embDomain_comapDomain hs

theorem projectiveCodimensionComponent_eq_zero_of_off_grade (z : X.carrier →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → X.supportCodimension (irreducibleSetEquivPoints.symm x) ≠ p) :
    projectiveCodimensionComponent X p z = 0 := by
  ext Z
  change z (Chow.BundleCycles.cyclePointEmbedding X p Z) = 0
  by_contra hn
  apply hz (Chow.BundleCycles.cyclePointEmbedding X p Z) hn
  change X.supportCodimension (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z.val)) = p
  rw [irreducibleSetEquivPoints.symm_apply_apply]
  exact Z.property

def projectivePointChowClass : (X.carrier →₀ ℚ) →ₗ[ℚ] Chow.BundleCycles.ChowQ X p :=
  (Chow.BundleCycles.cycleToChowQ X p).comp (projectiveCodimensionComponent X p)

theorem projectivePointChowClass_pointCycle (z : X.RationalDimensionCycle p) :
    projectivePointChowClass X p (Chow.BundleCycles.pointCycle X p z) = Chow.BundleCycles.cycleToChowQ X p z := by
  change Chow.BundleCycles.cycleToChowQ X p (projectiveCodimensionComponent X p (Chow.BundleCycles.pointCycle X p z)) = _
  rw [projectiveCodimensionComponent_pointCycle]

theorem projectivePointChowClass_principal (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    projectivePointChowClass X p (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) = 0 := by
  change Chow.BundleCycles.cycleToChowQ X p (projectiveCodimensionComponent X p (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0
  by_cases hp : X.supportCodimension W + 1 = p
  · apply Chow.BundleCycles.cycleToChowQ_principalDivisor
    refine ⟨W, hp, g, hg, ?_⟩
    exact pointCycle_codimensionComponent_supported X p _ (fun x hx =>
      (schemePrincipalPointDivisor_codimension X W g x hx).trans hp)
  · rw [projectiveCodimensionComponent_eq_zero_of_off_grade, map_zero]
    intro x hx
    rw [schemePrincipalPointDivisor_codimension X W g x hx]
    exact hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionPointClass.BundleCycles
