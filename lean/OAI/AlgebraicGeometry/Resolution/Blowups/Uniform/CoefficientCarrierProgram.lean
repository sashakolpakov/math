import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CarrierCommonAmbientProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf

/-! # Coefficient Carrier Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientCarrierProgram.Construction

noncomputable section

/-! Intrinsic coefficient programs from any established dimension retain their actual ambient carrier lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure UniformCoefficientCarrierProgram {d : ℕ} (𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (s : 𝒮.Schedule (n + 1).factorial β)
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData)
    [Smooth (H.subschemeι ≫ f)] (D : β → X.IdealSheafData)
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) where
  endpoint : Scheme
  structureMap : endpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  ideal : endpoint.IdealSheafData
  coefficientPrefix : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1).factorial H.subscheme (H.subschemeι ≫ f)
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι) endpoint structureMap ideal
  program : 𝒮.Program s (H.subschemeι ≫ f) (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (fun l => (D l).comap H.subschemeι) coefficientPrefix
  carrierMap : endpoint ⟶ Y
  comparison : P.CarrierComparison coefficientPrefix H.subschemeι carrierMap

theorem UniformCoefficientCarrierProgram.stepCount
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {s : 𝒮.Schedule (n + 1).factorial β} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J H : X.IdealSheafData} [Smooth (H.subschemeι ≫ f)] {D : β → X.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (A : UniformCoefficientCarrierProgram 𝒮 s f J H D P) : P.stepCount = (𝒮.incidenceTrace s).length :=
  (A.comparison.stepCount_eq P A.coefficientPrefix H.subschemeι A.carrierMap).trans
    ((𝒮.hasTrace A.program).stepCount A.coefficientPrefix _ (𝒮.incidenceTrace s))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientCarrierProgram.Construction
