import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineOpenChartDimension
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicParameterDifferential
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SubmersionCoordinates
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

/-! # Intrinsic Section Chart -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicSectionChart.Constructions

noncomputable section

/-!
# DegreeTwo: native scheme charts with the actual divisor section as coordinate

Regular affine charts of the fixed native dimension lift through the
actual affine-open map. The normal coordinate change therefore retains
complex differentiability on the scheme's native manifold.
-/

open scoped ContDiff _root_.Topology _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]

local instance nativeSectionChartIntegral : IsIntegral X.toOver.left := inferInstanceAs (IsIntegral X.carrier)
local instance nativeSectionChartSmooth : Smooth X.toOver.hom := X.smooth

/-- The actual section equation becomes a normal coordinate in a chart
of the native scheme manifold, contained in its original analytic open. -/
theorem exists_native_section_chart_smooth (U : X.carrier.Opens) (hU : IsAffineOpen U)
    (p b : Γ(X.carrier, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U))
        (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ))
      (q : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
        (ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker)),
      x.val ∈ q.source ∧ q x.val = 0 ∧ q.source ⊆ (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set _) ∧
      (∀ z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U, z.val ∈ q.source → (q z.val).1 = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p z) ∧
      q.MDifferentiable 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ)
        𝓘(ℂ, ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker) ∧
      ContMDiffOn 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ)
        𝓘(ℂ, ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker) ∞ q q.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker)
        𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ) ∞ q.symm q.target := by
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val, x.property⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U
  let hAdomain : IsDomain A := by
    change IsDomain Γ(X.carrier, U)
    infer_instance
  let hAsmooth : Algebra.Smooth ℂ A := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth X.structureMap U hU
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X.toOver U hU
  let : IsOpenImmersion i.left := by
    change IsOpenImmersion hU.fromSpec
    infer_instance
  let E := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU
  let y := E.symm x
  have hiy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y = x.val := by
    rw [← AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_val X U hU]
    exact congrArg Subtype.val (E.apply_symm_apply x)
  have heval (a : Γ(X.carrier, U)) : y a = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U a x := by
    have h := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation X U hU y a
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U a (E (E.symm x)) = y a at h
    rw [E.apply_symm_apply] at h
    exact h.symm
  obtain ⟨e, he, hye⟩ := AffineOpenChartDimension.Constructions.exists_affineOpen_regularChart_nativeDimension A i y
  have hyp : y p = 0 := (heval p).trans hxp
  have hyb : y b ≠ 0 := by rwa [heval b]
  have hs := @IntrinsicParameterDifferential.Constructions.parameter_fderiv_surjective_in_regularChart A inferInstance hAdomain
    inferInstance hAsmooth p b hp hsm _ e he y hye hyp hyb
  have hfp := (he.1 p).contDiffAt (e.open_target.mem_nhds (e.map_source hye))
  obtain ⟨r, hr, hry, hrf, hrc, hri⟩ :=
    SubmersionCoordinates.Constructions.exists_analytic_submersion_coordinates (fun z => e.symm z p) (e y) hfp hs
  let c := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e
  have hc : c ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X.toOver
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) := ⟨U, hU, e, he, rfl⟩
  have hxc : x.val ∈ c.source := ⟨y, hye, hiy⟩
  have hcx : c x.val = e y := by
    rw [← hiy]
    exact ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply A i e y
  let q := c.trans r
  have hxq : x.val ∈ q.source := by
    refine ⟨hxc, ?_⟩
    change c x.val ∈ r.source
    rwa [hcx]
  refine ⟨e, q, hxq, ?_, ?_, ?_, ?_⟩
  · change r (c x.val) = 0
    rw [hcx, hry, e.left_inv hye, hyp]
    rfl
  · intro z hz
    obtain ⟨w, _, hw⟩ := hz.1
    have hv := (E w).property
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (E w).val ∈ U at hv
    rw [AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_val X U hU, hw] at hv
    exact hv
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := hz.1
    have hEz : E w = z := by
      apply Subtype.ext
      exact (AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_val X U hU w).trans hwz
    change (r (c z.val)).1 = _
    rw [hrf, ← hwz, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply, e.left_inv hw]
    rw [← hEz]
    exact (AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation X U hU w p).symm
  · let I := 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ)
    let J := 𝓘(ℂ, ℂ × (fderiv ℂ (fun z => e.symm z p) (e y)).ker)
    have hcc : ContMDiffOn I I ∞ c c.source :=
      contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
    have hci : ContMDiffOn I I ∞ c.symm c.target :=
      contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
    have hqf : ContMDiffOn I J ∞ q q.source :=
      (hrc.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffOn.comp
        (hcc.mono Set.inter_subset_left) (fun _ hz => hz.2)
    have hqi : ContMDiffOn J I ∞ q.symm q.target :=
      hci.comp ((hri.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffOn.mono
        Set.inter_subset_left) (fun _ hz => hz.2)
    exact ⟨⟨hqf.mdifferentiableOn (by simp), hqi.mdifferentiableOn (by simp)⟩, hqf, hqi⟩

/-- The native complex differentiability consequence of the actual smooth
normal-chart construction. -/
theorem exists_native_section_chart (U : X.carrier.Opens) (hU : IsAffineOpen U)
    (p b : Γ(X.carrier, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U))
        (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ))
      (q : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
        (ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker)),
      x.val ∈ q.source ∧ q x.val = 0 ∧ q.source ⊆ (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U : Set _) ∧
      (∀ z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U, z.val ∈ q.source → (q z.val).1 = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p z) ∧
      q.MDifferentiable 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.toOver.hom) → ℂ)
        𝓘(ℂ, ℂ × (fderiv ℂ (fun z => e.symm z p)
          (e ((AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU).symm x))).ker) := by
  obtain ⟨e, q, hxq, hqx, hqU, hq, hqd, _, _⟩ :=
    exists_native_section_chart_smooth X U hU p b hp hsm x hxp hxb
  exact ⟨e, q, hxq, hqx, hqU, hq, hqd⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicSectionChart.Constructions
