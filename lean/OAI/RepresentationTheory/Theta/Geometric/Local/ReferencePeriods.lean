import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedKernel
import OAI.RepresentationTheory.Theta.Geometric.KernelLineStability

/-! # Reference Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Holomorphic reference ball coordinates near an actual reference
fiber, using its original full field and lattice marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.exists_holomorphic_reference_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (O : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (period : Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, period z ∈ D.domain ∧
        (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
          (R.transportedReferenceLabel f H z₀ hz₀) z).ker =
            Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} := by
  let p := H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
    (R.transportedReferenceLabel f H z₀ hz₀)
  obtain ⟨V, period, hV, hzV, hVU, hhol, hk⟩ := KernelLineStability.exists_holomorphic_kernel_line_of_finrank_one
    p H.compatible.neighborhood H.compatible.isOpen
    (H.referenceMarkedMatrix_holomorphic D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀)) z₀ z₀.property a.val
    (R.transportedReferenceMatrix_center f H z₀ hz₀)
    (fun z hz => R.transportedReferenceMatrix_finrank f H z₀ hz₀ hs hdegree ⟨z, hz⟩)
  have heq : period z₀ = a.val := AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine.lineVector_span_injective
    ((hk z₀ hzV).symm.trans (R.transportedReferenceMatrix_center f H z₀ hz₀))
  let O := V ∩ period ⁻¹' (D.domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
  refine ⟨O, period, hhol.continuousOn.isOpen_inter_preimage hV D.domain.isOpen,
    ⟨hzV, ?_⟩, (fun z hz => hVU hz.1), hhol.mono Set.inter_subset_left, heq, ?_⟩
  · change period z₀ ∈ D.domain
    rw [heq]
    exact a.property
  · intro z hz
    exact ⟨hz.2, hk z hz.1⟩

end

end OAI.RepresentationTheory.Theta.Geometric
