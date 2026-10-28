import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.IncidenceCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabelComposition

/-! # Incidence Surface Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram.Construction

noncomputable section

/-! A complete prescribed-level surface program records each canonical incidence refinement and uses common labels between levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive UniformIncidenceSurfaceProgram (n : ℕ) :
    (m : ℕ) → (β : Type) → [Fintype β] →
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K → Prop
  | terminal {m : ℕ} {β : Type} [Fintype β] {X : Scheme}
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {D : β → X.IdealSheafData}
      (hstop : m < (n + 1).factorial) (E : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
      (ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤) :
      UniformIncidenceSurfaceProgram n m β X f J D X f J .stop
  | refine {ℓ : ℕ} {β : Type} [Fintype β] {X : Scheme}
      [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {D : β → X.IdealSheafData}
      (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
      (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
      (AM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (A.surfaceCenter ℓ hb hd hlevel) D)
      {Y Z : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {K : Y.IdealSheafData} {L : Z.IdealSheafData}
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K)
      (hcenters : P.followsCenters (A.surfaceIncidenceCenters ℓ hb hd hlevel D))
      (hcount : P.stepCount = Fintype.card (Finset β)) (hP : P.uniformBoundaryCompatible β D)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) Y g K Z h L)
      (tail : UniformIncidenceSurfaceProgram n ℓ (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β)
        Y g K (P.boundaryAtLength D (Fintype.card (Finset β)) hcount) Z h L Q) :
      UniformIncidenceSurfaceProgram n (ℓ + 1) β X f J D Z h L (P.append Q)

namespace UniformIncidenceSurfaceProgram

theorem uniformBoundaryCompatible
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) : P.uniformBoundaryCompatible β D := by
  induction T with
  | terminal hstop E ht => exact ⟨E⟩
  | refine A hb hd hlevel AM P hcenters hcount hP Q tail ih =>
      exact P.append_uniformBoundaryCompatible_fixed_labels Q _ hP _ hcount ih

theorem terminal_order
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  induction T with
  | terminal hstop E ht => exact ht
  | refine A hb hd hlevel AM P hcenters hcount hP Q tail ih => exact ih

end UniformIncidenceSurfaceProgram

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram.Construction
