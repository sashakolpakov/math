import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualSchedule
import OAI.AlgebraicGeometry.Resolution.Blowups.TraceCompanionResidualDrop

/-! # Residual Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualProgram.Construction

noncomputable section

/-! Recorded residual programs combine exact changes of control with continuation on a residual-order neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive SurfaceResidualProgram (b : ℕ) :
    {m : ℕ} → {β : Type} → [Fintype β] → [DecidableEq β] → {a : β → ℕ} →
    ResidualSchedule.Construction.SurfaceResidualSchedule b m β a →
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J I : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K → Prop
  | monomial {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ)
      (S : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a [Finset.univ])
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
      {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
      (H : Boundary.MonomialProgram.Construction.BoundaryMonomialProgram b β a [Finset.univ] S X f I D Y g K P) :
      SurfaceResidualProgram b (.monomial a S) X f J I D Y g K P
  | higher {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hle : b ≤ m + 1)
      (S : HistorySchedule.Construction.SurfaceHistorySchedule m (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.residualExponents a (m + 1) b))
      {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J I : X.IdealSheafData} {J' I' : Y.IdealSheafData} {K : Z.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m + 1) X f J Y g J')
      (order : PositiveSurface.Construction.PositiveSurfaceOrderProgram (m + 1) β S X f J D Y g J' A)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g I') (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m + 1) b A P)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g I' Z h K)
      (tail : SurfaceResidualProgram b schedule Y g J' I'
        (A.boundaryAtLength D S.incidenceTrace.length (order.hasIncidenceTrace.stepCount A D S.incidenceTrace)) Z h K R) :
      SurfaceResidualProgram b (.higher a hle S schedule) X f J I D Z h K (P.append R)
  | companion {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hlt : m + 1 < b)
      (S : HistorySchedule.Construction.SurfaceHistorySchedule ((m + 1) * (b - (m + 1)) - 1)
        (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.companionExponents a (m + 1) b))
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth g]
      {J I : X.IdealSheafData} {C J' I' : Y.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix ((m + 1) * (b - (m + 1))) X f
        (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b) Y g C)
      (order : PositiveSurface.Construction.PositiveSurfaceOrderProgram ((m + 1) * (b - (m + 1))) β S X f
        (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b) D Y g C A)
      (B : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m + 1) X f J Y g J')
      (sameB : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups ((m + 1) * (b - (m + 1))) (m + 1) A B)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g I')
      (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups ((m + 1) * (b - (m + 1))) b A P)
      {V Z : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData} {M : Z.IdealSheafData}
      (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1))
        ((Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι ≫ g) (I'.comap (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι) V h L)
      (tail : SurfaceResidualProgram b schedule (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1))
        ((Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι ≫ g)
        (J'.comap (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι) (I'.comap (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι)
        (fun l => (A.boundaryAtLength D S.incidenceTrace.length
          (order.hasIncidenceTrace.stepCount A D S.incidenceTrace) l).comap (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι) V h L T)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g I' Z k M) (r : V ⟶ Z)
      (comparison : R.EtaleComparison T (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι r)
      (hstart : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g I' (b - 1)).support : Set Y) ⊆
        Set.range (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι)
      (hcover : letI : Smooth k := R.endpoint_smooth
        ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M (b - 1)).support : Set Z) ⊆ Set.range r) :
      SurfaceResidualProgram b (.companion a hlt S schedule) X f J I D Z k M (P.append R)

namespace SurfaceResidualProgram

theorem terminal_order {b : ℕ} (hb : 0 < b) {m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.SurfaceResidualProgram b schedule X f J I D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  induction H with
  | monomial a S H => exact H.terminal_order hb
  | higher a hle S schedule A order P same R tail ih => exact ih
  | companion a hlt S schedule A order B sameB P same T tail R r comparison hstart hcover ih =>
      exact comparison.terminal_order_of_endpoint_cover R T _ r (b - 1) hcover ih

theorem hasIncidenceTrace {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.SurfaceResidualProgram b schedule X f J I D Y g K P) :
    P.HasIncidenceTrace β D schedule.incidenceTrace := by
  induction H with
  | monomial a S H => exact H.hasIncidenceTrace
  | higher a hle S schedule A order P same R tail ih =>
      exact same.append_traceAtLength A P R _ _ order.hasIncidenceTrace _ rfl _ ih
  | companion a hlt S schedule A order B sameB P same T tail R r comparison hstart hcover ih =>
      have hA := order.hasIncidenceTrace
      have hAB := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible A _ (hA.uniformBoundaryCompatible A _ _)
      obtain ⟨EA⟩ := A.boundaryAtLength_atlas _ hAB _ (hA.stepCount A _ _)
      have hR := R.hasIncidenceTrace_of_order_neighborhood T _ r comparison hstart _ _ EA _ ih
      exact same.append_traceAtLength A P R _ _ hA _ rfl _ hR

theorem uniformBoundaryCompatible {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.SurfaceResidualProgram b schedule X f J I D Y g K P) : P.uniformBoundaryCompatible β D :=
  H.hasIncidenceTrace.uniformBoundaryCompatible P D schedule.incidenceTrace

end SurfaceResidualProgram

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualProgram.Construction
