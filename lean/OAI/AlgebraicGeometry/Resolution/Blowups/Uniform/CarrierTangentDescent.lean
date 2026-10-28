import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientCarrierProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.PointedCarrierCommonProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixDescent

/-! # Carrier Tangent Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Actual surface coefficient carrier lifts descend across pointed changes of maximal contact. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_endpointIso_of_tangent_comparisons
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J H H' : X.IdealSheafData} [IsIntegral H.subscheme]
    [Smooth (H.subschemeι ≫ f)] [Smooth (H'.subschemeι ≫ f)]
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K} {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y' g' K'}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (A' : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H' D P')
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hH : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) (hdH : topologicalKrullDim H.subscheme ≤ d)
    (hcompare : ∀ x : X, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support →
      Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt f J H H' D n x)) :
    ∃ e : Y' ≅ Y, P.EtaleComparison P' (𝟙 X) e.hom ∧
      ∀ r : Y' ⟶ Y, P.EtaleComparison P' (𝟙 X) r → r = e.hom := by
  apply P.exists_endpointIso_of_pointed_tangent P' (A.stepCount.trans A'.stepCount.symm)
  intro x hx
  obtain ⟨B⟩ := hcompare x hx
  have hxH : B.left B.point ∈ H.support := by
    rw [B.point_eq]
    exact Scheme.IdealSheafData.support_antitone hH hx
  obtain ⟨R, j, hj, p, hp, S', s, C, P0, u, u', haP, hbP⟩ :=
    𝒮.exists_pointed_common_ambient_program _ _ hC rfl rfl D P P'
      A.coefficientPrefix A'.coefficientPrefix A.program A'.program A.carrierMap A'.carrierMap
      A.comparison A'.comparison B.ambient B.left B.right B.ground B.ideal B.carrier B.boundary hdH B.point hxH
  refine ⟨Spec R, S', (j ≫ B.left) ≫ f, s, J.comap (j ≫ B.left), C, P0,
    j ≫ B.left, j ≫ B.right, u, u', p, ?_, B.congruence.comp j, haP, hbP⟩
  change B.left (j p) = x
  rw [hp, B.point_eq]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
