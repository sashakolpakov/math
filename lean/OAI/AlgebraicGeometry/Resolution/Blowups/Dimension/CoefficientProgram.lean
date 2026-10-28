import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.SameEtalePullbackExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.TerminalSourcePrefixComparison

/-! # Coefficient Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientProgram.Construction

noncomputable section

/-! Dimension-indexed coefficient phases retain their homogeneous atlas witness and have unique full programs for a common schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure DimensionCoefficientProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : 𝒮.Schedule (n + 1).factorial β)
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) : Prop where
  trace : P.HasIncidenceTrace β D (𝒮.incidenceTrace schedule)
  terminal : letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤
  witness : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ ∨
    ∃ (L : Y.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g L),
      Nonempty (Modeled.UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D Q) ∧
        Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (n + 1) (n + 1) Q P

theorem DimensionCoefficientProgram.exists_endpointIso
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K} {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y' g' K'}
    (A : DimensionCoefficientProgram 𝒮 schedule f J D P) (B : DimensionCoefficientProgram 𝒮 schedule f J D P') :
    ∃ e : Y' ≅ Y, P.EtaleComparison P' (𝟙 X) e.hom ∧
      ∀ r : Y' ⟶ Y, P.EtaleComparison P' (𝟙 X) r → r = e.hom := by
  have hN : P.stepCount = P'.stepCount :=
    (A.trace.stepCount P D (𝒮.incidenceTrace schedule)).trans (B.trace.stepCount P' D (𝒮.incidenceTrace schedule)).symm
  rcases A.witness with ht | ⟨L, Q, ⟨AQ⟩, hs⟩
  · exact P.exists_endpointIso_of_terminal_source P' hN ht
  rcases B.witness with ht | ⟨L', Q', ⟨BQ⟩, hs'⟩
  · exact P.exists_endpointIso_of_terminal_source P' hN ht
  obtain ⟨e, he, _⟩ := AQ.exists_endpointIso BQ
  have hcomp := hs.etaleComparison hs' (𝟙 X) e.hom he (Scheme.IdealSheafData.comap_id J)
  exact ⟨e, hcomp, fun r hr => hr.endpoint_unique P P' (𝟙 X) r e.hom hcomp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientProgram.Construction
