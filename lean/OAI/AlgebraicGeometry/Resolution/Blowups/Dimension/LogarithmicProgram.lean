import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCenterIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceFixedComposition

/-! # Logarithmic Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgram.Construction

noncomputable section

/-! Full logarithmic programs combine canonical component clearing with a lower-dimensional coefficient schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def DimensionLogarithmicSchedule {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] : Type 1 :=
  𝒮.Schedule (n + 1).factorial (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β)

def dimensionLogarithmicIncidenceTrace {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d}
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : DimensionLogarithmicSchedule 𝒮 n β) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β :=
  (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β).appendAtLength (Fintype.card (Finset β))
    (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length β) (𝒮.incidenceTrace schedule)

def DimensionLogarithmicSchedule.stepCount {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d}
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : DimensionLogarithmicSchedule 𝒮 n β) : ℕ :=
  Fintype.card (Finset β) + (𝒮.incidenceTrace schedule).length

theorem dimensionLogarithmicIncidenceTrace_length {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d}
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : DimensionLogarithmicSchedule 𝒮 n β) :
    (dimensionLogarithmicIncidenceTrace schedule).length = schedule.stepCount :=
  Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length _ _ _ _

inductive DimensionLogarithmicProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : DimensionLogarithmicSchedule 𝒮 n β) :
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K → Prop
  | component {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {D : β → X.IdealSheafData}
      (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f A.center D)
      {Y Z : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {K : Y.IdealSheafData} {L : Z.IdealSheafData}
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K)
      (hcenters : P.followsCenters (A.componentIncidenceCenters D))
      (hcount : P.stepCount = Fintype.card (Finset β)) (hP : P.uniformBoundaryCompatible β D)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) Y g K Z h L)
      (tail : letI : Smooth g := P.endpoint_smooth
        CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule g K (P.boundaryAtLength D _ hcount) Q) :
      DimensionLogarithmicProgram 𝒮 schedule X f J D Z h L (P.append Q)

namespace DimensionLogarithmicProgram

theorem hasIncidenceTrace
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : DimensionLogarithmicSchedule 𝒮 n β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P) :
    P.HasIncidenceTrace β D (dimensionLogarithmicIncidenceTrace schedule) := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      let : Smooth _ := P.endpoint_smooth
      have hhead := A.componentIncidenceCenters_hasTrace _ AM P hcenters
      exact hhead.appendAtLength P Q _ _ _ (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length _) _ tail.trace

theorem uniformBoundaryCompatible
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : DimensionLogarithmicSchedule 𝒮 n β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P) :
    P.uniformBoundaryCompatible β D :=
  T.hasIncidenceTrace.uniformBoundaryCompatible P D _

theorem terminal_order
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : DimensionLogarithmicSchedule 𝒮 n β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      let : Smooth _ := P.endpoint_smooth
      exact tail.terminal

theorem stepCount
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : DimensionLogarithmicSchedule 𝒮 n β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P) :
    P.stepCount = schedule.stepCount :=
  (T.hasIncidenceTrace.stepCount P D _).trans (dimensionLogarithmicIncidenceTrace_length schedule)

end DimensionLogarithmicProgram

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgram.Construction
