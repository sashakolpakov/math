import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedBall
import OAI.RepresentationTheory.Theta.Geometric.KernelLineStability

/-! # Intrinsic Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual reference markings give holomorphic coordinates for the exact
original Hodge line near a reference point of a native test family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.KernelLineStability

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso

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

theorem Models.FinePELModel.exists_holomorphic_native_reference_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ z₀.val ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      DifferentiableOn ℂ period O ∧ period z₀ = a.val ∧
      ∀ z ∈ O, period z ∈ P.domain ∧
        (H.referenceMarkedMatrix P hP
          (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
            Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} := by
  let p := H.referenceMarkedMatrix P hP
    (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀)
  have hd (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ H.compatible.neighborhood) :
      Module.finrank ℂ (p z).ker = 1 := by
    obtain ⟨b, hb⟩ := M.transportedNativeReferenceKernel_ball hM κ hP hκ f a H z₀ hz₀ hs hdegree ⟨z, hz⟩
    change Module.finrank ℂ (H.referenceMarkedMatrix P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker = 1
    rw [hb]
    exact finrank_span_singleton (Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero b.val)
  obtain ⟨V, period, hV, hzV, hVU, hhol, hk⟩ := RepresentationTheory.Theta.Geometric.KernelLineStability.exists_holomorphic_kernel_line_of_finrank_one
    p H.compatible.neighborhood H.compatible.isOpen
    (H.referenceMarkedMatrix_holomorphic P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀)) z₀ z₀.property a.val
    (M.transportedNativeReferenceMatrix_center hM κ hP hκ f a H z₀ hz₀) hd
  have heq : period z₀ = a.val := NegativeLine.lineVector_span_injective
    ((hk z₀ hzV).symm.trans (M.transportedNativeReferenceMatrix_center hM κ hP hκ f a H z₀ hz₀))
  let O := V ∩ period ⁻¹' P.domain
  refine ⟨O, period, hhol.continuousOn.isOpen_inter_preimage hV P.domain_isOpen,
    ⟨hzV, ?_⟩, (fun _ hz => hVU hz.1), hhol.mono Set.inter_subset_left, heq, ?_⟩
  · change period z₀ ∈ P.domain
    rw [heq]
    exact a.property
  · intro z hz
    exact ⟨hz.2, hk z hz.1⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
