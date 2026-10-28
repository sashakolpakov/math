import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MarkedKernelImages
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PELComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallChart
import OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse
import OAI.RepresentationTheory.Theta.Geometric.Relative.FieldEquiv
import OAI.RepresentationTheory.Theta.Geometric.Relative.IntegralPolarization
import OAI.RepresentationTheory.Theta.Geometric.Relative.RationalExponential
import OAI.RepresentationTheory.Theta.Geometric.KernelLineStability

/-! # Local Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LocalPeriods

noncomputable section

/-! Transport an arbitrary full field marking in a native family chart.
Its lattice, polarization and ordered exponential labels remain fixed,
and its active Hodge line gives local holomorphic ball coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.Manifold

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local implicit_reducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods

section Transport

variable {E : Type} [Field E] [NumberField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

namespace NativeFamilyHolomorphicTransport

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F) (z₀ : H.compatible.neighborhood)
    (m₀ : let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking (z : H.compatible.neighborhood) :
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  exact m₀.trans (H.compatible.fieldBetween A ρ z₀ z)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking_apply (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    H.transportedFieldMarking z₀ m₀ z v = H.compatible.rationalBetween A ρ z₀ z (m₀ v) := by
  unfold Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking
  rw [LinearEquiv.trans_apply, RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldBetween_apply]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking_center : H.transportedFieldMarking z₀ m₀ z₀ = m₀ := by
  apply LinearEquiv.ext
  intro v
  rw [H.transportedFieldMarking_apply]
  change H.rationalTransport z₀ ((H.rationalTransport z₀).symm (m₀ v)) = m₀ v
  exact (H.rationalTransport z₀).apply_symm_apply (m₀ v)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldLabel : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C) := by
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
  exact (H.rationalTransport z₀).symm.toLinearMap.comp (m₀.restrictScalars ℚ).toLinearMap

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldLabel_value (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    H.rationalTransport z (H.transportedFieldLabel z₀ m₀ v) =
      H.transportedFieldMarking z₀ m₀ z v := by
  rw [H.transportedFieldMarking_apply]
  rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldLabel_complex (z : H.compatible.neighborhood)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((H.transportedFieldLabel z₀ m₀).baseChange ℂ u) =
        ((H.transportedFieldMarking z₀ m₀ z).restrictScalars ℚ).toLinearMap.baseChange ℂ u := by
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  have he : (H.rationalTransport z).toLinearMap.comp (H.transportedFieldLabel z₀ m₀) =
      ((H.transportedFieldMarking z₀ m₀ z).restrictScalars ℚ).toLinearMap := by
    apply LinearMap.ext
    exact H.transportedFieldLabel_value z₀ m₀ z
  dsimp only
  rw [← he, LinearMap.baseChange_comp]
  rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking_integral (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    H.transportedFieldMarking z₀ m₀ z v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety ↔
        m₀ v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety := by
  rw [H.transportedFieldMarking_apply]
  exact H.compatible.rationalBetween_integral A ρ z₀ z (m₀ v)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking_polarization (z : H.compatible.neighborhood) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
      (H.transportedFieldMarking z₀ m₀ z v) (H.transportedFieldMarking z₀ m₀ z w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) (m₀ v) (m₀ w) := by
  rw [H.transportedFieldMarking_apply, H.transportedFieldMarking_apply]
  exact H.compatible.rationalBetween_polarization A ρ z₀ z (m₀ v) (m₀ w)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedFieldMarking_level (z : H.compatible.neighborhood)
    (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (c : Multiplicative (Fin (2 * g) → ZMod N)) (r : ℝ)
    (hc : RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint A.level (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)) c =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
          (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety.toOver)
          (r • (m₀ v).val)) :
    RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint A.level (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) c =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
          (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
          (r • (H.transportedFieldMarking z₀ m₀ z v).val) := by
  have he := H.compatible.fiberBetween_level A ρ z₀ z c
  rw [hc, H.compatible.fiberBetween_rational_exp] at he
  exact he.symm

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.nativeModuliChart_of_local_periods [IsIntegral S.left] [Smooth S.hom]
    {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ Y) [Mono f]
    (D : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (q : D → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hO : IsOpen O) (hcenter : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ O) (hOU : O ⊆ H.compatible.neighborhood)
    (hhol : DifferentiableOn ℂ period O)
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (hmod : ∀ z ∈ O, ∃ hz : period z ∈ D, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = q ⟨period z, hz⟩) :
    ∃ e : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart,
      x ∈ e.source ∧ e x = period (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) ∧
      e.MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
        (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧ e.target ⊆ D ∧
      ∀ y ∈ e.source, ∃ hy : e y ∈ D, y ≫ f = q ⟨e y, hy⟩ := by
  have hi : Set.InjOn period O := by
    intro z hz w hw heq
    obtain ⟨hpz, hzpoint⟩ := hmod z hz
    obtain ⟨hpw, hwpoint⟩ := hmod w hw
    have hzw : (⟨period z, hpz⟩ : D) = ⟨period w, hpw⟩ := Subtype.ext heq
    rw [hzw] at hzpoint
    exact RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_injective C (H.compatible.subset_chart (hOU hz))
      (H.compatible.subset_chart (hOU hw)) ((cancel_mono f).mp (hzpoint.trans hwpoint.symm))
  have hd : Module.finrank ℂ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) = Module.finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart := by
    rw [C.dimension, hdim]
    simp only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Fintype.card_fin]
  let p := RepresentationTheory.Theta.Geometric.InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hd hO hhol hi
  have hp : p.MDifferentiable (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr hhol,
      mdifferentiableOn_iff_differentiableOn.mpr
        (RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse.injectiveHolomorphicPartialHomeomorph_inverse hd hO hhol hi)⟩
  let c := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart C
  let e := c.trans p
  have hxc : x ∈ c.source := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center_mem C
  have hcx : c x = RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C := RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center C
  refine ⟨e, ⟨hxc, ?_⟩, ?_, (RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_holomorphic C).trans hp, ?_, ?_⟩
  · change c x ∈ O
    rw [hcx]
    exact hcenter
  · change period (c x) = period (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)
    rw [hcx]
  · intro b hb
    have hbp : b ∈ period '' O := hb.1
    obtain ⟨z, hz, rfl⟩ := hbp
    exact (hmod z hz).choose
  · intro y hy
    obtain ⟨hpy, hmy⟩ := hmod (c y) hy.2
    have hparam : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (c y) = y := c.left_inv hy.1
    refine ⟨hpy, ?_⟩
    rwa [hparam] at hmy

variable [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedMarkedMatrix_kernel (z : H.compatible.neighborhood) :
    (H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
      (H.transportedFieldLabel z₀ m₀) z).ker =
        ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s
          (H.transportedFieldMarking z₀ m₀ z) P hP).comp e₀.toLinearMap).ker := by
  ext v
  change H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
    (H.transportedFieldLabel z₀ m₀) z v = 0 ↔ _
  rw [H.markedKernelMatrix_kernel_iff, H.transportedFieldLabel_complex]
  rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedMarkedMatrix_center :
    (H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
      (H.transportedFieldLabel z₀ m₀) z₀).ker =
        ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) s m₀ P hP).comp e₀.toLinearMap).ker := by
  rw [H.transportedMarkedMatrix_kernel, H.transportedFieldMarking_center]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.transportedMarkedMatrix_finrank (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) (z : H.compatible.neighborhood)
    (hr : LieRanks.HasLieRank (A.abelian.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
      (ρ.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
      ((P.embeddings P.distinguished).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    Module.finrank ℂ (H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
      (H.transportedFieldLabel z₀ m₀) z).ker = 1 := by
  rw [H.transportedMarkedMatrix_kernel z₀ m₀ P hP e₀ z, LinearMap.ker_comp,
    Submodule.comap_equiv_eq_map_symm]
  exact (e₀.symm.finrank_map_eq _).trans
    (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection_finrank A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
      (H.transportedFieldMarking z₀ m₀ z) P hP hr)

end NativeFamilyHolomorphicTransport

end Transport

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ) (hP : P.IsAdmissible)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (A : PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ S))
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A.polarized A.action F)
    (z₀ : H.compatible.neighborhood)
    (m₀ : let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E]
        Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (a : P.domain)
    (hcenter : ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
      s m₀ P hP).comp e₀.toLinearMap).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val})

include hκ hcenter in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.exists_holomorphic_marked_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, period z ∈ P.domain ∧
        (H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
          (H.transportedFieldLabel z₀ m₀) z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} := by
  let p := H.markedKernelMatrix ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
    (H.transportedFieldLabel z₀ m₀)
  have hcenter' : (p z₀).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} :=
    (H.transportedMarkedMatrix_center z₀ m₀ P hP e₀).trans hcenter
  have hd (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ H.compatible.neighborhood) :
      Module.finrank ℂ (p z).ker = 1 := by
    apply H.transportedMarkedMatrix_finrank z₀ m₀ P hP e₀ hs rfl hdegree ⟨z, hz⟩
    exact A.complexFiber_distinguished_rank κ hκ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left
      (Complex.BallPeriods.restrictComplexBase_point κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) hP
  obtain ⟨V, period, hV, hzV, hVU, hhol, hk⟩ := RepresentationTheory.Theta.Geometric.KernelLineStability.exists_holomorphic_kernel_line_of_finrank_one
    p H.compatible.neighborhood H.compatible.isOpen
    (H.markedKernelMatrix_holomorphic ((RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP).comp e₀.toLinearMap)
      (H.transportedFieldLabel z₀ m₀)) z₀ z₀.property a.val hcenter' hd
  have heq : period z₀ = a.val := NegativeLine.lineVector_span_injective ((hk z₀ hzV).symm.trans hcenter')
  let O := V ∩ period ⁻¹' P.domain
  refine ⟨O, period, hhol.continuousOn.isOpen_inter_preimage hV P.domain_isOpen,
    ⟨hzV, ?_⟩, (fun _ hz => hVU hz.1), hhol.mono Set.inter_subset_left, heq, ?_⟩
  · change period z₀ ∈ P.domain
    rw [heq]
    exact a.property
  · intro z hz
    exact ⟨hz.2, hk z hz.1⟩

variable {T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (B : P.domain → PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ T))
    (y : P.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T)
    (mB : ∀ b : P.domain, let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule (B b).polarized (B b).action (y b)
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (y b)).variety)

include hκ hcenter in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.exists_holomorphic_marked_fiber_isos
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hi : ∀ b v,
      m₀ v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety ↔
        mB b v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (y b)).variety)
    (hp : ∀ b v w,
      RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (B b).polarized (y b) (mB b v) (mB b w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) (m₀ v) (m₀ w))
    (hk : ∀ b,
      ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (B b).polarized (B b).action (y b) s (mB b) P hP).comp
        e₀.toLinearMap).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})
    {I : Type*} (label : I → Multiplicative (Fin (2 * (3 * s)) → ZMod N))
    (hlabel : Function.Surjective label) (v : I → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hA : ∀ i, RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint A.polarized.level (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)) (label i) =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
          (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)).variety.toOver)
          ((N : ℝ)⁻¹ • (m₀ (v i)).val))
    (hB : ∀ b i, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint ((B b).polarized.pullback (y b).left) (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (y b)).variety.toOver)
        ((N : ℝ)⁻¹ • (mB b (v i)).val)) :
    ∃ (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, ∃ hz : period z ∈ P.domain,
        Nonempty (PEL.Objects.PELIso (A.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)))
          ((B ⟨period z, hz⟩).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (y ⟨period z, hz⟩)))) := by
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcenter, hker⟩ :=
    PEL.Objects.PELObject.exists_holomorphic_marked_periods κ hκ hP A H z₀ m₀ e₀ a hcenter hs hdegree
  refine ⟨O, period, hO, hzO, hOU, hhol, hcenter, ?_⟩
  intro z hz
  let b : P.domain := ⟨period z, (hker z hz).1⟩
  let z' : H.compatible.neighborhood := ⟨z, hOU hz⟩
  let m := H.transportedFieldMarking z₀ m₀ z'
  have hmi (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
      m u ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety ↔
        mB b u ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (B b).polarized (y b)).variety :=
    (H.transportedFieldMarking_integral z₀ m₀ z' u).trans (hi b u)
  have hmp (u w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
      RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (B b).polarized (y b) (mB b u) (mB b w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) (m u) (m w) :=
    (hp b u w).trans (H.transportedFieldMarking_polarization z₀ m₀ z' u w).symm
  have hmk :
      (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s m P hP).ker =
        (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (B b).polarized (B b).action (y b) s (mB b) P hP).ker := by
    apply PELComparison.fieldMarkingFirstProjection_kernel_eq_of_normalized κ hP A (B b)
      (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) (y b) m (mB b) e₀
    exact (H.transportedMarkedMatrix_kernel z₀ m₀ P hP e₀ z').symm.trans
      ((hker z hz).2.trans (hk b).symm)
  refine ⟨b.property, ⟨PELComparison.markedPELFiberIso κ hκ hP A (B b) (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) (y b)
    m (mB b) hs hdegree hmi hmp hmk label hlabel v ?_ (hB b)⟩⟩
  intro i
  rw [Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint_pullback]
  exact H.transportedFieldMarking_level z₀ m₀ z' (v i) (label i) (N : ℝ)⁻¹ (hA i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LocalPeriods
