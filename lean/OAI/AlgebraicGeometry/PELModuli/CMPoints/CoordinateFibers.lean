import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EstablishedComponent

/-! # Coordinate Fibers -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.CMPoints

/-! Retain the three specified rank-one coefficient types in the CM
point construction, so their actual factor maps can be specialized. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.Module
open scoped Classical

theorem PeriodComparison.UniversalPELPeriodChart.exists_coordinate_CM_point
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {hP : P.IsAdmissible} {iota : E →+* K} {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N}
    {κ : K →+* ℂ} {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {f : X.toOver ⟶ M.complexFiber κ}
    (T : PeriodComparison.UniversalPELPeriodChart P hP M κ X f) :
    ∃ x : X.analyticSpace,
      CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativeFinePELAt M κ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x)) := by
  obtain ⟨z, b, hb⟩ := PeriodOnBall.exists_CM_period_on_ball P hP T.matrix T.hermitian T.anisotropic
    T.normalizer T.normalizes
  refine ⟨T.cover z, CoordinateRealization.coordinateRealizationOfBasisPeriod P hP b (T.hodge z) (T.realization z)
    (fun x => (T.periods z x).trans (hb x).symm), ?_⟩
  exact T.fiber z

theorem CoordinateFibers.exists_coordinate_CM_point_on_finePEL_component
    (hperiod : PeriodComparison.UniversalPELPeriodComparisonInput)
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (iota : E →+* K) (κ : K →+* ℂ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hiota : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N) (hM : M.IsFine)
    (hball : M.HasProjectiveBallComponents κ) (C : M.ComplexComponent κ) :
    ∃ x : M.ComplexPoints κ, ConnectedComponents.mk x = C ∧
      CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativeFinePELAt M κ x) := by
  obtain ⟨X, ⟨hdim, f, hopen, hclosed, hrange⟩, _⟩ := hball C
  obtain ⟨T⟩ := hperiod E K s N P hP iota κ M hiota hN hM C X f hdim hopen hclosed hrange
  obtain ⟨x, hx⟩ := T.exists_coordinate_CM_point
  refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x, ?_, hx⟩
  have hm : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := ⟨x, rfl⟩
  rw [hrange] at hm
  exact hm

theorem CoordinateFibers.exists_in_clopen_range_of_every_component
    {X Y : Type*} [TopologicalSpace Y] (f : X → Y) (hclopen : IsClopen (Set.range f))
    (x₀ : X) (P : Y → Prop)
    (hP : ∀ C : ConnectedComponents Y, ∃ y, ConnectedComponents.mk y = C ∧ P y) :
    ∃ x, P (f x) := by
  obtain ⟨y, hy, hPy⟩ := hP (ConnectedComponents.mk (f x₀))
  obtain ⟨x, hx⟩ := hclopen.connectedComponent_subset ⟨x₀, rfl⟩
    (ConnectedComponents.coe_eq_coe'.mp hy)
  exact ⟨x, hx ▸ hPy⟩

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.exists_coordinate_CM_point_over_numberField_on_component
    [IsGalois ℚ E] (hCMAbelianVariety : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    ∃ (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.integralComplexComponent a t)) (F : Subfield ℂ),
      NumberField F ∧
      CoordinateRealization.HasCoordinateCMRealization (M.datum a) (hM.2.2 a).1
        (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t) x)) ∧
      ∃ p : Spec (.of F) ⟶ (M.embeddedGenericComponent a t).left,
        Spec.map (CommRingCat.ofHom F.subtype) ≫ p = M.embeddedComponentPoint a t x := by
  obtain ⟨hP, hiota, hN, hFine, hball, _⟩ := hM.2.2 a
  obtain ⟨x, hx⟩ := CoordinateFibers.exists_in_clopen_range_of_every_component
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.integralComplexComponentFinePELMap a t))
    (M.integralComplexComponentFinePELMap_clopen_range a t)
    (M.integralComplexComponentBasePoint a t)
    (fun y => CoordinateRealization.HasCoordinateCMRealization (M.datum a) hP
      (IntrinsicFiber.nativeFinePELAt (M.moduli a) M.complexEmbedding y))
    (EstablishedComponent.exists_proved_coordinate_CM_point_on_finePEL_component (M.datum a) hP hM.1 hM.2.1 M.iota
      M.complexEmbedding (M.moduli a) hiota hN hFine hball)
  have hCM := (M.embeddedComponentPoint_hasCMH1_iff hM a t x).mpr hx.hasCMH1
  obtain ⟨F, hF, p, hp⟩ := M.component_CM_point_descends hCMAbelianVariety hM a t
    (M.embeddedComponentPoint a t x) hCM
  exact ⟨x, F, hF, hx, p, hp⟩

end AlgebraicGeometry.PELModuli.CMPoints

namespace AlgebraicGeometry.PELModuli.CMPoints.CoordinateFibers

/-! The specified coordinate CM realization transports through actual
scheme isomorphisms, with its Hodge comparison retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem coordinateCMRealization_iso_iff
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible} {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (e : A.toOver ≅ B.toOver) :
    CoordinateRealization.HasCoordinateCMRealization P hP A ↔ CoordinateRealization.HasCoordinateCMRealization P hP B :=
  ⟨CoordinateRealization.HasCoordinateCMRealization.of_iso e.symm, CoordinateRealization.HasCoordinateCMRealization.of_iso e⟩

theorem nativePolarizedAt_pullback_coordinateCM_iff
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible}
    {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (Q : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T) :
    CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativePolarizedAt (Q.pullback f) p) ↔
      CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativePolarizedAt Q (p ≫ f)) :=
  coordinateCMRealization_iso_iff (IntrinsicFiber.nativePolarizedAtPullbackIso Q f p)

theorem nativePolarizedAt_iso_coordinateCM_iff
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible}
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {Q T : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : Q.abelian.scheme ≅ T.abelian.scheme) (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativePolarizedAt Q p) ↔
      CoordinateRealization.HasCoordinateCMRealization P hP (IntrinsicFiber.nativePolarizedAt T p) :=
  coordinateCMRealization_iso_iff (IntrinsicFiber.nativePolarizedAtIsoOfIso e p)

end AlgebraicGeometry.PELModuli.CMPoints.CoordinateFibers

end

end OAI
