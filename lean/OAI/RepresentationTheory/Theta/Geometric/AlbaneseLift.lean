import OAI.RepresentationTheory.Theta.Geometric.Period.AlbaneseMap
import OAI.RepresentationTheory.Theta.Geometric.AlbaneseClosedFormLift
import OAI.RepresentationTheory.Theta.Geometric.PeriodClosed
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants

/-! # Albanese Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The descended theta form lifts to an actual algebraic Albanese form.
Its pullback recovers the theta form and vanishes on every other component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

def Data.ActiveHeckeThetaData.periodThetaPureClosedLinear :
    D.sphericalInputs →ₗ[ℂ]
      AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 :=
  (D.periodThetaClosedLinear X cover hcover hh ha).codRestrict _
    (D.periodThetaSmoothForm_bidegree X cover hcover hh ha)

def Data.ActiveHeckeThetaData.componentThetaAlgebraicLift : D.sphericalInputs →ₗ[ℂ]
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms (D.pel.actualComplexComponentAlbaneseVariety hg j).toOver :=
  (AlbaneseClosedFormLift.algebraicLiftClosedHolomorphic X (D.pel.actualComplexComponentAlbaneseVariety hg j)
    (D.periodComponentAlbaneseMap hg j X component)
    (D.periodComponentAlbaneseMap_betti_bijective hg j X component)).comp
      (D.periodThetaPureClosedLinear X cover hcover hh ha)

def Data.ActiveHeckeThetaData.thetaAlbaneseLift : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseProjection j)).comp
    (D.componentThetaAlgebraicLift hg j X component cover hcover hh ha)

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_component_pullback (φ : D.sphericalInputs) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ)) =
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.periodComponentAlbaneseMap hg j X component)
      (D.componentThetaAlgebraicLift hg j X component cover hcover hh ha φ) := by
  change (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j) ∘ₗ
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseMap hg) ∘ₗ
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseProjection j))) _ = _
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, ← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp,
    Category.assoc, D.componentAlbanese_coordinate_self hg j]
  rfl

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_closed_pullback (φ : D.sphericalInputs) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization X
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) =
      D.periodThetaClosedLinear X cover hcover hh ha φ := by
  rw [D.thetaAlbaneseLift_component_pullback]
  exact AlbaneseClosedFormLift.algebraicLiftClosedHolomorphic_pullback X
    (D.pel.actualComplexComponentAlbaneseVariety hg j)
    (D.periodComponentAlbaneseMap hg j X component)
    (D.periodComponentAlbaneseMap_betti_bijective hg j X component)
    (D.periodThetaPureClosedLinear X cover hcover hh ha φ)

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_complement (i : Fin D.pel.componentCount) (hij : i ≠ j)
    (φ : D.sphericalInputs) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)
      (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ)) = 0 := by
  change (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i) ∘ₗ
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseMap hg) ∘ₗ
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.pel.complexAlbaneseProjection j))) _ = _
  rw [← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, ← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, D.componentAlbanese_coordinate_ne hg i j hij,
    CategoryTheory.Hom.one_def, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_constant]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
