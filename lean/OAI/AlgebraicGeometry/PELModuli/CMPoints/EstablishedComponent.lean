import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodMatrixFiber
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyPeriodMatrices
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FamilyClassifying
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Established Component -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedComponent

noncomputable section

section

/-! The original smooth integral PEL base of complex dimension two
contains a coordinate CM fiber. All analytic charts, full native
period matrices, rational labels, and ball comparisons are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.CategoryTheory.MonObj

theorem exists_coordinate_CM_fiber_on_smooth_PEL_base
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K] {s N r : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (hP : P.IsAdmissible) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (basis : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (f : Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) ⟶ M.space)
    (hinj : Function.Injective (FamilyClassifying.PELFamilyClassifyingPoint M κ f))
    (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ∃ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, CoordinateRealization.HasCoordinateCMRealization P hP
      (PolarizedIntrinsicPresentation.polarizedNativePresentation (M.universal.pullback (FamilyClassifying.PELFamilyClassifyingPoint M κ f x)).polarized).variety := by
  let G := M.universal.polarized.abelian.pullback f.left
  let present := FamilyClassifying.PELFamilyPresentation M κ f
  obtain ⟨C⟩ := IntrinsicFamilyCharts.exists_native_family_charts G s₀
  let E' := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.charts.relativePresentation.presentation.map → ℂ
  let F' := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ
  let N' := C.charts.charts
  let parameter := fun q : F' => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra C.openMap (N'.charts.base.symm q)
  obtain ⟨n, d, U, hU, hqU, hUN, marking, coordinates, matrix, hhol, _, hsurj, hker⟩ :=
    IntrinsicFamilyPeriodMatrices.exists_native_family_holomorphic_period_matrices (E := E') (F := F') G present
      C.charts.affineOpen C.charts.isAffine C.openMap C.charts.projection_eq
      C.charts.sectionAlgebra C.charts.section_eq N'
  let p := fun q : F' => FamilyClassifying.PELFamilyClassifyingPoint M κ f (parameter q)
  have hp : Set.InjOn p U := by
    intro q hq q' hq' he
    have hp' : parameter q = parameter q' := hinj he
    have he' := (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap C.algebra C.openMap).injective hp'
    exact N'.charts.base.symm.injOn (N'.withinBase (hUN hq)) (N'.withinBase (hUN hq')) he'
  have hF : Module.finrank ℂ F' = Module.finrank ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart := by
    have h := C.dimension.trans hdim
    simpa [F', Geometry.ComplexBall.PrescribedSignsB.BallChart] using h
  obtain ⟨q, hq⟩ := IntrinsicPeriodMatrixFiber.exists_coordinate_CM_fiber_of_native_period_matrices hP hs hdegree
    M hM κ hκ basis U hU ⟨_, hqU⟩ hF p hp marking matrix hhol hsurj hker
  exact ⟨parameter q, hq⟩

end

/-! Every original projective PEL surface component contains the
specified coordinate CM fiber, proved from the actual universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem exists_coordinate_CM_point_on_projective_PEL_piece
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K] {s N : ℕ} [NeZero N]
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hκ : κ.comp iota = P.μ) (hM : M.IsFine)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (hdim : X.complexDimension = 2)
    (f : X.toOver ⟶ M.complexFiber κ) [IsOpenImmersion f.left] :
    ∃ x : X.analyticSpace, CoordinateRealization.HasCoordinateCMRealization P hP
      (IntrinsicFiber.nativeFinePELAt M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let b : Module.Basis (Fin (Module.finrank ℤ (NumberField.RingOfIntegers E))) ℤ
      (NumberField.RingOfIntegers E) := Module.finBasis ℤ (NumberField.RingOfIntegers E)
  have hdim' : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom = 2 := hdim
  obtain ⟨x, hx⟩ := exists_coordinate_CM_fiber_on_smooth_PEL_base (S := X.toOver)
    hP hs hdegree M hM κ hκ b hdim'
    (FamilyClassifying.PELComplexFamilyMap M κ f) (FamilyClassifying.PELFamilyClassifyingPoint_injective M κ f)
    (Classical.arbitrary X.analyticSpace)
  rw [FamilyClassifying.PELFamilyClassifyingPoint_complexMap] at hx
  let p := IntrinsicFiber.finePELComplexPoint M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)
  let A := M.universal.polarized.pullback p
  let iso : (IntrinsicFiber.nativePolarizedAt M.universal.polarized p).toOver ≅
      (PolarizedIntrinsicPresentation.polarizedNativePresentation A).variety.toOver :=
    IntrinsicFiber.nativePolarizedAtIso M.universal.polarized p ≪≫ (PolarizedIntrinsicPresentation.polarizedNativePresentation A).comparison
  exact ⟨x, CoordinateRealization.HasCoordinateCMRealization.of_iso iso hx⟩

theorem exists_proved_coordinate_CM_point_on_finePEL_component
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K] {s N : ℕ}
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hκ : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine)
    (hball : M.HasProjectiveBallComponents κ) (C : M.ComplexComponent κ) :
    ∃ x : M.ComplexPoints κ, ConnectedComponents.mk x = C ∧
      CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativeFinePELAt M κ x) := by
  let : NeZero N := ⟨by have h := hN.1; omega⟩
  obtain ⟨X, ⟨hdim, f, hopen, _, hrange⟩, _⟩ := hball C
  let : IsOpenImmersion f.left := hopen
  obtain ⟨x, hx⟩ := exists_coordinate_CM_point_on_projective_PEL_piece P hP hs hdegree
    iota κ M hκ hM X hdim f
  refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x, ?_, hx⟩
  have hm : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := ⟨x, rfl⟩
  rw [hrange] at hm
  exact hm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedComponent
