import OAI.AlgebraicGeometry.Resolution.Blowups.Component.IncidenceCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceLength

/-! # Logarithmic Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgram.Construction

noncomputable section

/-! A full logarithmic surface program starts with canonical component clearing and then follows prescribed coefficient levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive SurfaceLogarithmicProgram (n m : ℕ) (β : Type) [Fintype β] :
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
      (tail : Uniform.IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β)
        Y g K (P.boundaryAtLength D (Fintype.card (Finset β)) hcount) Z h L Q) :
      SurfaceLogarithmicProgram n m β X f J D Z h L (P.append Q)

def surfaceLogarithmicProgramStepCount (n m k : ℕ) : ℕ :=
  2 ^ k + Uniform.IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount n m (k + 2 ^ k)

namespace SurfaceLogarithmicProgram

theorem uniformBoundaryCompatible
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P) : P.uniformBoundaryCompatible β D := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      exact P.append_uniformBoundaryCompatible_fixed_labels Q _ hP _ hcount tail.uniformBoundaryCompatible

theorem terminal_order
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  cases T with
  | component A AM P hcenters hcount hP Q tail => exact tail.terminal_order

theorem stepCount
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P) :
    P.stepCount = surfaceLogarithmicProgramStepCount n m (Fintype.card β) := by
  classical
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      rw [Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_stepCount, hcount, tail.stepCount, Uniform.IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels, Fintype.card_finset]
      rfl

end SurfaceLogarithmicProgram

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgram.Construction
