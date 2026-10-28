import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ProgramIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceCarrier
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistorySchedule

/-! # Auxiliary Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! An auxiliary surface program has one exact incidence trace including the retained old boundary label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace (n ℓ : ℕ) (β : Type) [Fintype β] [DecidableEq β] (j : β) :
    Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β :=
  (ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n ℓ {l : β // l ≠ j}).adjoinCarrier.reindex β
    (Equiv.optionSubtypeNe j).symm.toEmbedding

theorem AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace_length (n ℓ : ℕ) (β : Type) [Fintype β] [DecidableEq β] (j : β) :
    (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace n ℓ β j).length = HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β) := by
  rw [AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace, Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.reindex_length,
    Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.adjoinCarrier_length, ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace_length]
  have hcard : Fintype.card {l : β // l ≠ j} = Fintype.card β - 1 := by
    have he := Fintype.card_congr (Equiv.optionSubtypeNe j)
    rw [Fintype.card_option] at he
    omega
  rw [hcard]
  rfl

theorem AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram.hasIncidenceTrace
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData} {j : β}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) :
    P.HasIncidenceTrace β D (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace n ℓ β j) := by
  classical
  let γ := {l : β // l ≠ j}
  let E : γ → X.IdealSheafData := fun l => D l.val
  have hT : P.HasIncidenceTrace γ E (ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n ℓ γ) :=
    LogarithmicProgram.Construction.SurfaceLogarithmicProgram.hasIncidenceTrace T
  let e : Option γ ≃ β := Equiv.optionSubtypeNe j
  let F : Option γ → X.IdealSheafData := fun l => match l with | none => D j | some s => E s
  have hF (l : Option γ) : F l = D (e l) := by cases l <;> rfl
  let AF : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f F [Finset.univ] :=
    A.pullbackLabels (fun l => some (e l))
      (fun l l' s hl hl' => e.injective (Option.some_injective _ (hl.trans hl'.symm))) F hF
  have hPF : P.HasIncidenceTrace (Option γ) F (ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n ℓ γ).adjoinCarrier :=
    hT.adjoin_auxiliary_carrier (Nat.succ_pos n) P J (D j) rfl γ E _
      (by convert AF using 1)
  have ht := hPF.reindex P (Option γ) β F _ e.symm.toEmbedding
  change P.HasIncidenceTrace β (fun l => F (e.symm l)) (AuxiliaryIncidenceTrace.Construction.auxiliarySurfaceIncidenceTrace n ℓ β j) at ht
  have heq : (fun l => F (e.symm l)) = D := by
    funext l
    exact (hF (e.symm l)).trans (congrArg D (e.apply_symm_apply l))
  rwa [heq] at ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
