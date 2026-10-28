import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPEL
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ObjectTestFiberMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LocalPeriods

/-! # Ball Local Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallLocalRecovery.FinePELModel

noncomputable section

/-! Native local recovery for the full negative-ball family built from
an arbitrary original PEL object. All markings and moduli points belong
to the actual objects, with their original ordered level structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj _root_.Manifold

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
  Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver
attribute [local irreducible] Models.FinePELModel.complexTestFamily Intrinsic.ChernPairing.nativePolarizationForm RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm
  PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap ChangedPELModel.RealChangedPEL.action ChangedPELModel.RealChangedPEL.fullLevel
  Models.FinePELModel.objectTestFieldMarking Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    {A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))}
    {hs : 0 < s} {hdegree : Module.finrank ℚ E = 2 * s}
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint (a : P.domain) : M.ComplexPoints κ :=
  M.objectPoint hM κ (D.fiberAt hP a).object

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hy : y ≫ f = M.realBallPoint hM κ D hP a)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallTestFieldMarking :
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety :=
  M.objectTestFieldMarking hM κ f (D.fiberAt hP a).object y hy (D.fiberAt hP a).fieldMarking

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallTestFieldMarking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.realBallTestFieldMarking hM κ D hP f a y hy v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety ↔
        ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm v).val ∈
          HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)) := by
  exact (M.objectTestFieldMarking_integral hM κ f (D.fiberAt hP a).object y hy
    (D.fiberAt hP a).fieldMarking v).trans ((D.fiberAt hP a).marking_integral v)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallTestFieldMarking_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized y
      (M.realBallTestFieldMarking hM κ D hP f a y hy v) (M.realBallTestFieldMarking hM κ D hP f a y hy w) =
        Intrinsic.ChernPairing.nativePolarizationForm A.polarized
          ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm v)
          ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm w) := by
  exact (M.objectTestFieldMarking_polarization hM κ f (D.fiberAt hP a).object y hy
    (D.fiberAt hP a).fieldMarking v w).trans
      ((D.fiberAt hP a).marking_polarization (D.pointTransport hP a).property.1 v w)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallTestFieldMarking_kernel :
    ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y s
      (M.realBallTestFieldMarking hM κ D hP f a y hy) P hP).comp D.normalizer.toLinearMap).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
  let F := D.fiberAt hP a
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule F.object.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized) F.object.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower F.object.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized) F.object.action
  let m : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.object.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized)) :=
    F.fieldMarking
  let mr : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.object.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized)) :=
    F.marking
  ext v
  have hk := M.objectTestFieldMarking_first_kernel hM κ f F.object y hy m
    hP D.normalizer v
  have hm : (m.restrictScalars ℚ).toLinearMap = mr.toLinearMap := by
    apply LinearMap.ext
    intro u
    exact F.fieldMarking_apply u
  have hu : RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP (D.normalizer v) =
      PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer v :=
    RepresentationTheory.Theta.Geometric.Reference.FirstStandardCoordinates.referenceFirstComplexInclusion_eq_standard P hP (D.normalizer v)
  have hsrc : (m.restrictScalars ℚ).toLinearMap.baseChange ℂ
      (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP (D.normalizer v)) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection
          (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.object.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized))).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
    have harg := congrArg (fun l : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
        (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.object.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized)) =>
      l.baseChange ℂ (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP (D.normalizer v))) hm
    have harg' := harg.trans (congrArg (mr.toLinearMap.baseChange ℂ) hu)
    exact (congrArg (fun u => u ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native F.object.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation F.object.polarized))).ker)
        harg').to_iff.trans (D.fiberAt_kernel hP a v)
  exact hk.trans hsrc

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallTestFieldMarking_level (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) :
    RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level y
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y)
      (ChangedPELModel.RealChangedPEL.originalLevelLabel A l) =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
          (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver)
          ((N : ℝ)⁻¹ • (M.realBallTestFieldMarking hM κ D hP f a y hy
            (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree
              (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) l))).val) := by
  let F := D.fiberAt hP a
  apply M.objectTestFieldMarking_level hM κ f F.object y hy F.fieldMarking
  have h := F.marking_level l
  apply Over.OverMorphism.ext
  change ((F.object.polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
    (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (ChangedPELModel.RealChangedPEL.originalLevelLabel A l))).val.left ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact congrArg Over.Hom.left h

variable [IsGalois ℚ E] (hκ : κ.comp iota = P.μ)

include hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_holomorphic_realBall_moduli_periods
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (ha : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.realBallPoint hM κ D hP a) :
    ∃ (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, ∃ hz : period z ∈ P.domain,
        RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = M.realBallPoint hM κ D hP ⟨period z, hz⟩ := by
  let q := M.realBallPoint hM κ D hP
  let m₀ := M.realBallTestFieldMarking hM κ D hP f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) ha
  let B (b : P.domain) := M.complexTestFamily κ (q b)
  let yB (_ : P.domain) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) := 𝟙 _
  let mB (b : P.domain) := M.realBallTestFieldMarking hM κ D hP (q b) b (yB b) (Category.id_comp (q b))
  let label := ChangedPELModel.RealChangedPEL.originalLevelLabel A
  let v (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) := PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action
    s hs rfl hdegree (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) l)
  have hcenter := M.realBallTestFieldMarking_kernel hM κ D hP f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) ha
  have hi (b : P.domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
      m₀ u ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety ↔
      mB b u ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (yB b)).variety :=
    (M.realBallTestFieldMarking_integral hM κ D hP f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) ha u).trans
      (M.realBallTestFieldMarking_integral hM κ D hP (q b) b (yB b) (Category.id_comp (q b)) u).symm
  have hp (b : P.domain) (u w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
      RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (B b).polarized (yB b) (mB b u) (mB b w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) (m₀ u) (m₀ w) :=
    (M.realBallTestFieldMarking_polarization hM κ D hP (q b) b (yB b) (Category.id_comp (q b)) u w).trans
      (M.realBallTestFieldMarking_polarization hM κ D hP f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) ha u w).symm
  have hk (b : P.domain) :
      ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (B b).polarized (B b).action (yB b) s (mB b) P hP).comp
        D.normalizer.toLinearMap).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val} :=
    M.realBallTestFieldMarking_kernel hM κ D hP (q b) b (yB b) (Category.id_comp (q b))
  have hA (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) :
      RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
        (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)) (label l) =
          HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
            (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety.toOver)
            ((N : ℝ)⁻¹ • (m₀ (v l)).val) :=
    M.realBallTestFieldMarking_level hM κ D hP f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) ha l
  have hB (b : P.domain) (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))) :
      Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint ((B b).polarized.pullback (yB b).left) (label l) =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (yB b)).variety.toOver)
          ((N : ℝ)⁻¹ • (mB b (v l)).val) := by
    rw [Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint_pullback]
    exact M.realBallTestFieldMarking_level hM κ D hP (q b) b (yB b) (Category.id_comp (q b)) l
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcent, hiso⟩ :=
    PEL.Objects.PELObject.exists_holomorphic_marked_fiber_isos κ hκ hP (M.complexTestFamily κ f) H z₀ m₀
      D.normalizer a hcenter B yB mB hs hdegree hi hp hk label
      (ChangedPELModel.RealChangedPEL.originalLevelLabel_surjective A) v hA hB
  refine ⟨O, period, hO, hzO, hOU, hhol, hcent, ?_⟩
  intro z hz
  obtain ⟨hzp, ⟨e⟩⟩ := hiso z hz
  refine ⟨hzp, ?_⟩
  have he := Models.FinePELModel.point_eq_of_testFiber_iso (κ := κ) (x := RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    (y := yB ⟨period z, hzp⟩) (M := M) (hM := hM) f (q ⟨period z, hzp⟩) e
  simpa only [yB, q, Category.id_comp] using he

include hκ hy in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_native_realBall_moduli_chart [IsIntegral S.left] [Smooth S.hom] [Mono f]
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2) :
    ∃ e : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart,
      y ∈ e.source ∧ e y = a.val ∧
      e.MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
        (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧ e.target ⊆ P.domain ∧
      ∀ z ∈ e.source, ∃ hz : e z ∈ P.domain,
        z ≫ f = M.realBallPoint hM κ D hP ⟨e z, hz⟩ := by
  obtain ⟨C, F, ⟨H⟩⟩ := Intrinsic.HolomorphicTransport.exists_native_family_holomorphic_transport
    (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action y (NeZero.pos N)
  let z₀ : H.compatible.neighborhood := ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩
  have h₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.realBallPoint hM κ D hP a := by
    change RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) ≫ f = _
    rw [RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_center]
    exact hy
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcent, hmod⟩ :=
    M.exists_holomorphic_realBall_moduli_periods hM κ D hP f a hκ H z₀ h₀
  obtain ⟨e, hye, he, hdiff, htarget, hrecovery⟩ :=
    H.nativeModuliChart_of_local_periods f P.domain (M.realBallPoint hM κ D hP)
      O period hO hzO hOU hhol hdim hmod
  exact ⟨e, hye, he.trans hcent, hdiff, htarget, hrecovery⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallLocalRecovery.FinePELModel
