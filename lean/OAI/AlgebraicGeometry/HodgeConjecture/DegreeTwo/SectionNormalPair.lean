import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterNormalPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Section Normal Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionNormalPair.Constructions

noncomputable section

/-!
# DegreeTwo: normal pairs for actual scheme-section equations

The actual affine character chart transfers the normal equation to the
same analytic open used in the Chern and rational-section constructions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- On the principal smooth neighborhood of an actual section's zero locus,
its native analytic evaluation is the normal coordinate of a genuine pair. -/
theorem exists_section_normalPair (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (U : X.carrier.Opens) (hU : IsAffineOpen U) (p b : Γ(X.carrier, U)) (hp : p ≠ 0)
    (hsm : letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
      Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)))
    (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0)
    (hxb : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b x ≠ 0) :
    ∃ (d : ℕ) (N : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
      (Subtype.val : {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U // DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} → DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
      ⟨x, hxp⟩),
      (∀ y ∈ N.neighborhood, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b y ≠ 0) ∧
      ∀ y : N.neighborhood, N.normalCoordinate y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val := by
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val, x.property⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
  let : Smooth X.structureMap := X.smooth
  let : Algebra.Smooth ℂ Γ(X.carrier, U) := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth X.structureMap U hU
  let hAsmooth : Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) :=
    Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth X.structureMap U hU
  let hAdomain : IsDomain (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) := by
    change IsDomain Γ(X.carrier, U)
    infer_instance
  let : Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)) := hsm
  let e := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU
  let y := e.symm x
  have heval (a : Γ(X.carrier, U)) (z : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :
      e.symm z a = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U a z := by
    have he := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation X U hU (e.symm z) a
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U a (e (e.symm z)) = e.symm z a at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  have hyp : y p = 0 := (heval p x).trans hxp
  have hyb : y b ≠ 0 := by rwa [heval b x]
  obtain ⟨d, r, hyr, hry, hrb, hr⟩ := @LocalParameterNormalPair.Constructions.exists_local_parameter_equationChart
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) inferInstance hAdomain inferInstance hAsmooth
    p b hp hsm y hyp hyb
  let q := e.symm.transOpenPartialHomeomorph r
  have hxq : x ∈ q.source := hyr
  have hqx : q x = 0 := hry
  have hq : ∀ z ∈ q.source, (q z).2 = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p z := by
    intro z hz
    exact (hr (e.symm z) hz).trans (heval p z)
  obtain ⟨N, hchart, hN⟩ := EquationNormalPair.Constructions.exists_equation_normalPair_with_chart
    (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p) x hxp q hxq hqx hq
  refine ⟨d, N, ?_, hN⟩
  intro z hz
  have hs := N.neighborhood_subset_source hz
  rw [hchart] at hs
  have hb := hrb hs
  change e.symm z b ≠ 0 at hb
  rwa [heval b z] at hb

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionNormalPair.Constructions
