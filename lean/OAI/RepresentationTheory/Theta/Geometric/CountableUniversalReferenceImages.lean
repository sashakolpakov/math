import OAI.RepresentationTheory.Theta.Geometric.CountableUniversalCharts
import OAI.RepresentationTheory.Theta.Geometric.CountableReferenceIsoCharts
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.FiberIso
import OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates

/-! # Countable Universal Reference Images -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Reference points occurring in an actual smooth moduli subspace
are covered by countably many holomorphic images from its fixed dimension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA) (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] (f : S ⟶ D.pel.complexSpace)

theorem Data.ActiveHeckeThetaData.exists_countable_universal_reference_images :
    let V := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set V) (period : I → V → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ a : D.domain, (∃ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, y ≫ f = D.referenceModuliMap hg a) →
        ∃ i, a.val ∈ period i '' O i := by
  obtain ⟨T, hT, hcover⟩ := CountableUniversalCharts.exists_countable_universal_transport_cover D.pel hg f
  let : Countable T := hT.to_subtype
  have hex (c : T) := (Universal.HolomorphicTransport.complexUniversalHolomorphicTransport D.pel hg f c.val).exists_countable_reference_iso_charts
    D.pel.reference hg.reference_admissible
  choose I hI O period hO hmatch using hex
  let (c : T) : Countable (I c) := hI c
  let e (c : T) := FixedFamilyBaseCoordinates.fixedFamilyBaseCoordinates (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f c.val)
  let J := Σ c : T, I c
  refine ⟨J, inferInstance, fun i => e i.1 ⁻¹' O i.1 i.2, fun i v => period i.1 i.2 (e i.1 v),
    ?_, ?_⟩
  · intro i
    exact ⟨(hO i.1 i.2).1.preimage (e i.1).continuous,
      (hO i.1 i.2).2.2.comp (e i.1).differentiable.differentiableOn (fun _ hv => hv)⟩
  · intro a ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨c, z, hz⟩ := hcover y
    let R := D.referencePELPointData hg a
    have hzpoint : Intrinsic.FamilyFrames.familyChartParameter (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f c.val) z ≫ f = R.point :=
      (congrArg (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => t ≫ f) hz).trans hy
    let iso := R.nativeUniversalFiberIso f
      (Intrinsic.FamilyFrames.familyChartParameter (Universal.FamilyPeriodCharts.complexUniversalFamilyCharts D.pel f c.val) z) hzpoint
    obtain ⟨i, hzi, hip⟩ := hmatch c (D.referenceDomainPoint a) (R.analytic.toNativeReference D)
      (R.model.toNativeReferenceModel R.analytic) z iso
      (R.nativeUniversalFiberIso_group f _ hzpoint)
    refine ⟨⟨c, i⟩, (e c).symm z.val, ?_, ?_⟩
    · change e c ((e c).symm z.val) ∈ O c i
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hzi
    · change period c i (e c ((e c).symm z.val)) = a.val
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hip

end

end OAI.RepresentationTheory.Theta.Geometric
