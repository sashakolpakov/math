import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricTheta
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
import OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange

/-! # Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Forms

noncomputable section

/-!
# Native GeometricTheta operators, component restriction, and extended theta forms

These objects are constructed on GeometricTheta's actual schemes and Betti cohomology.
No projector, component restriction, theta extension, or commutation property
is supplied independently of the explicit GeometricTheta conclusion.

The native algebraic one-forms are not identified with Betti classes here:
that requires a de Rham comparison for TateComparison's affine-test Kähler-form model.
Neither ThetaOneForms nor the GeometricTheta output supplies that comparison. Likewise the
arithmetic Newton comparison and the relation to the specified CM type are
not conclusions of GeometricTheta. Those gaps are not represented by proof fields.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

/-- The rational active action is the actual TateComparison Betti action restricted
along GeometricTheta's special-linear algebra isomorphism. -/
def activeBettiAction (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] Module.End ℚ D.pel.H1 :=
  A.cohomologyAction.comp (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e)

theorem activeBettiAction_commute (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (a b : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Commute (activeBettiAction D A e a) (activeBettiAction D A e b) := by
  change Commute
    (A.cohomologyAction ((RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e) a))
    (A.cohomologyAction ((RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e) b))
  exact (show Commute ((RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e) a)
      ((RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e) b) from
    AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors _ _).map A.cohomologyAction

/-- Pullback along the actual component-to-total-Albanese morphism. -/
def componentRestriction (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount) :
    D.pel.H1 →ₗ[ℚ] PELModuli.IntegralModel.Product.bettiQ (D.componentComplex j) 1 :=
  PELModuli.IntegralModel.Product.bettiPullbackQ
    (D.componentComplexInclusion j ≫ D.pel.complexAlbaneseMap hg) 1

theorem componentRestriction_eq (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    componentRestriction D hg j =
      (PELModuli.IntegralModel.Product.bettiPullbackQ (D.componentComplexInclusion j) 1).comp
        (PELModuli.IntegralModel.Product.bettiPullbackQ (D.pel.complexAlbaneseMap hg) 1) :=
  PELModuli.IntegralModel.Product.bettiPullbackQ_comp _ _ _

theorem ballH1Projector_idempotent (j : Fin D.pel.componentCount) :
    (D.ballH1Projector j).comp (D.ballH1Projector j) = D.ballH1Projector j := by
  unfold RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ballH1Projector
  rw [← PELModuli.IntegralModel.Product.bettiPullbackQ_comp, ← Functor.map_comp, ← Functor.map_comp,
    RepresentationTheory.Theta.Geometric.Geometry.productCoordinateIdempotent_comp]

theorem ballH1ComplexProjector_idempotent (j : Fin D.pel.componentCount) :
    (D.ballH1ComplexProjector j).comp (D.ballH1ComplexProjector j) =
      D.ballH1ComplexProjector j := by
  unfold RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ballH1ComplexProjector
  rw [← LinearMap.baseChange_comp, ballH1Projector_idempotent]

/-- The actual total-space algebraic theta form supplied by the Albanese lift. -/
def extendedThetaForms (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) :
    D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsSpace :=
  (D.pel.albanesePullback hg).comp Θ

/-- Holomorphy of the actual canonical theta covector in period coordinates. -/
theorem native_theta_holomorphic (hhol : D.HasHolomorphicThetaData)
    (φ : D.sphericalInputs) :
    DifferentiableOn ℂ (D.thetaUniversal φ.val) D.domain :=
  RepresentationTheory.Theta.Geometric.LinearTheta.canonical_oneForm_holomorphic D.domain D.period hhol.1 D.project hhol.2 φ.val

theorem canonicalTheta_zero_on_other_components
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (i : Fin D.pel.componentCount) (hi : i ≠ j) (φ : D.sphericalInputs) :
    AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)
      (extendedThetaForms D hg Θ φ) = 0 := hΘ.2.2 i hi φ

/-- Extract actual native objects from the full, explicitly assumed GeometricTheta
output. The component idempotence is proved from its scheme construction. -/
theorem native_objects_of_GeometricTheta
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hGeometricTheta : GeometricTheta.Intrinsic.GeometricThetaOutput D hg hq hIsogenyQuotient) :
    ∃ (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
      (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
      (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA),
      A.IsRealization D.pel hg hq hIsogenyQuotient ∧
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ ∧
      (D.ballH1Projector j).comp (D.ballH1Projector j) = D.ballH1Projector j ∧
      (∀ h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
          (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h)) ∧
      (∀ i : Fin D.pel.componentCount, i ≠ j → ∀ φ : D.sphericalInputs,
        AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)
          (extendedThetaForms D hg Θ φ) = 0) := by
  obtain ⟨A, hA, e, _, _, _, j, X, component, cover, hdim, hcover, _, hcomm,
    _, _, Θ, hΘ, _, _⟩ := hGeometricTheta
  exact ⟨A, e, j, X, component, cover, Θ, hA, hdim, hcover, hΘ,
    ballH1Projector_idempotent D j, hcomm,
    canonicalTheta_zero_on_other_components D hg j _ Θ hΘ⟩

/-- Apply the entire committed GeometricTheta proposition with its natural hypotheses,
then construct the native objects above. -/
theorem native_objects_of_committed_GeometricTheta
    [IsGalois ℚ E] [IsTopologicalGroup Ga]
    (hGeometricTheta : GeometricTheta.Intrinsic.GeometricThetaInput) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hcoordinates : D.HasFiniteCoordinates) (hholomorphic : D.HasHolomorphicThetaData)
    (hautomorphy : D.HasRationalThetaCovariance) (hArithmetic : DenseRange D.rationalFinite) :
    ∃ (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
      (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
        RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
      (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
      (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA),
      A.IsRealization D.pel hg hq hIsogenyQuotient ∧
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ ∧
      (D.ballH1Projector j).comp (D.ballH1Projector j) = D.ballH1Projector j ∧
      (∀ h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
          (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h)) ∧
      (∀ i : Fin D.pel.componentCount, i ≠ j → ∀ φ : D.sphericalInputs,
        AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)
          (extendedThetaForms D hg Θ φ) = 0) := by
  exact native_objects_of_GeometricTheta D hg hq hIsogenyQuotient
    (hGeometricTheta hs hdegree D hg hq hIsogenyQuotient hTateComparison hcoordinates hholomorphic hautomorphy hArithmetic)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Forms
