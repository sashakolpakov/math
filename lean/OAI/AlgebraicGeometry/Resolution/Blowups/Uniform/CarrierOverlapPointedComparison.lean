import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierData
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CarrierOverlapCommonProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ComparisonAt

/-! # Carrier Overlap Pointed Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Initial pointed carrier overlap data construct the actual comparison used for global gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.openComparisonAt_of_overlap_data
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X X' Y Y' Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f']
    {J H : X.IdealSheafData} {J' H' : X'.IdealSheafData}
    [IsIntegral H.subscheme] [IsIntegral H'.subscheme]
    [Smooth (H.subschemeι ≫ f)] [Smooth (H'.subschemeι ≫ f')]
    {D : β → X.IdealSheafData} {D' : β → X'.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K} {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X' f' J' Y' g' K'}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f J H D P)
    (A' : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule f' J' H' D' P')
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (hC' : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f' J' (n + 1) H'.subschemeι ≠ ⊥)
    (hdH : topologicalKrullDim H.subscheme ≤ d) (hdH' : topologicalKrullDim H'.subscheme ≤ d)
    (hmax : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (B : TangentCarrierData.Construction.TangentCarrierOverlapData f J H D f' J' H' D' n)
    (j : X ⟶ Z) (l : X' ⟶ Z) (hcomm : B.left ≫ j = B.right ≫ l)
    (x : X) (y : X') (z : B.ambient) (hx : B.left z = x) (hy : B.right z = y) :
    P.OpenComparisonAt P' j l x y := by
  obtain ⟨W, w, M, R, r, s, hr, hs⟩ := A.exists_common_program_on_tangent_overlap A'
    hC hC' hdH hdH' hmax B.structureMap B.ideal B.leftCarrier B.rightCarrier B.boundary
    B.left B.right B.left_ground B.right_ground B.left_ideal B.right_ideal
    B.left_carrier B.right_carrier B.left_boundary B.right_boundary B.comparison
  exact ⟨B.ambient, W, B.structureMap, w, B.ideal, M, R, B.left, B.right, r, s, z,
    hx, hy, hcomm, hr, hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
