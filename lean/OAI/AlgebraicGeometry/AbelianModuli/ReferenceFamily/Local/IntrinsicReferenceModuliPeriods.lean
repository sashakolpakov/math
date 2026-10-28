import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.IntrinsicPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.FiberLevelIso

/-! # Intrinsic Reference Moduli Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The exact local holomorphic reference coordinates recover the actual
fine-moduli point of every nearby test-family fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)

include hz₀ in
theorem Models.FinePELModel.exists_holomorphic_native_reference_moduli_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, ∃ hp : period z ∈ P.domain,
        RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = M.referencePoint hM κ hP hκ ⟨period z, hp⟩ := by
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcenter, hker⟩ :=
    M.exists_holomorphic_native_reference_periods hM κ hP hκ f a H z₀ hz₀ hs hdegree
  refine ⟨O, period, hO, hzO, hOU, hhol, hcenter, ?_⟩
  intro w hw
  have hp := (hker w hw).1
  exact ⟨hp, M.nativeReferenceFiber_moduli_point hM κ hP hκ f a H z₀ hz₀
    ⟨period w, hp⟩ ⟨w, hOU hw⟩ hs hdegree (hker w hw).2⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
