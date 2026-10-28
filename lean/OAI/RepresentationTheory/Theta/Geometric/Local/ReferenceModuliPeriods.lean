import OAI.RepresentationTheory.Theta.Geometric.Local.ReferencePeriods
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.ModuliPoint

/-! # Reference Moduli Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed local holomorphic reference coordinates classify
the original nearby universal PEL fibers at their actual moduli points. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
      (Universal.PELConditions.complexUniversalAction D.pel hg f) F)
    (z₀ : H.compatible.neighborhood) (hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point)

include hz₀ in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.exists_holomorphic_reference_moduli_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (O : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (period : Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, ∃ hp : period z ∈ D.domain,
        Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = D.referenceModuliMap hg ⟨period z, hp⟩ := by
  obtain ⟨O, period, hO, hzO, hOU, hhol, hcenter, hker⟩ :=
    R.exists_holomorphic_reference_periods f H z₀ hz₀ hs hdegree
  refine ⟨O, period, hO, hzO, hOU, hhol, hcenter, ?_⟩
  intro w hw
  have hp := (hker w hw).1
  let b : D.domain := ⟨period w, hp⟩
  let R' := D.referencePELPointData hg b
  refine ⟨hp, ?_⟩
  exact R.referenceFiber_moduli_point f H z₀ hz₀ R' ⟨w, hOU hw⟩ hs hdegree (hker w hw).2

end

end OAI.RepresentationTheory.Theta.Geometric
