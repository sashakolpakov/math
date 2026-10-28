import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientNamedPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.AuxiliaryPrefixBoundary
import Mathlib.Logic.Equiv.Option
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceCarrier
import OAI.AlgebraicGeometry.Resolution.Blowups.FixedLengthBoundaryHistory
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.AuxiliaryHistoryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabelComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceOpenDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.SameTraceComposition

/-! # History Program Auxiliary -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups.Dimension

/-! Canonical component clearing and scheduled coefficient phases commute with étale restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem LogarithmicProgram.Construction.DimensionLogarithmicProgram.exists_etaleComparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n β} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
    {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M}
    (S : LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule V h L E W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      cases S with
      | component B BM R hRcenters hRcount hR S rest =>
          let : Smooth _ := P.endpoint_smooth
          let : Smooth _ := R.endpoint_smooth
          let : IsIntegral _ := R.endpoint_integral
          let : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian R.toBase
          let : CompactSpace _ := QuasiCompact.compactSpace_of_compactSpace R.toBase
          have hlist := A.componentIncidenceCenters_comap_etale D AM q _ _ B E BM hstructure hJ hD
          have hRcenters' : R.followsCenters ((A.componentIncidenceCenters D).map (fun C => C.comap q)) := by
            rw [hlist]
            exact hRcenters
          obtain ⟨r, hr⟩ := P.exists_etaleComparison_of_followsCenters _ hcenters R q hstructure hJ hRcenters'
          obtain ⟨het, hpb, hK⟩ := hr.endpoint_pullback P R q r
          let : Etale r := het
          have hboundary := hr.boundaryAtLength P R q r β D E hD _ hcount hRcount
          have hover := congrArg (fun u => u ≫ f) hpb.w
          simp only [Category.assoc, P.over, hstructure, R.over] at hover
          obtain ⟨s, hs⟩ := tail.exists_etaleComparison rest r hover hK (fun l => congrFun hboundary l)
          exact ⟨s, hr.append P R q r Q S s hs⟩

end AlgebraicGeometry.Resolution.Blowups.Dimension

namespace AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary.Construction
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! Auxiliary programs use a lower-dimensional coefficient schedule and retain the full labelled boundary. -/

def DimensionAuxiliaryProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (j : β)
    (schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j})
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K) : Prop :=
  LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1))
    (fun l => D l.val) Y g K P

namespace DimensionAuxiliaryProgram

theorem uniformBoundaryCompatible
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}} {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) : P.uniformBoundaryCompatible β D := by
  classical
  let γ := {l : β // l ≠ j}
  let E : γ → X.IdealSheafData := fun l => D l.val
  have hT : P.uniformBoundaryCompatible γ E := LogarithmicProgram.Construction.DimensionLogarithmicProgram.uniformBoundaryCompatible T
  let e : Option γ ≃ β := Equiv.optionSubtypeNe j
  let F : Option γ → X.IdealSheafData := fun l => match l with | none => D j | some s => E s
  have hF (l : Option γ) : F l = D (e l) := by cases l <;> rfl
  let AF : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f F [Finset.univ] :=
    A.pullbackLabels (fun l => some (e l))
      (fun l l' s hl hl' => e.injective (Option.some_injective _ (hl.trans hl'.symm))) F hF
  have hPF : P.uniformBoundaryCompatible (Option γ) F :=
    P.uniformBoundaryCompatible_adjoin_auxiliary_carrier (Nat.succ_pos n) J (D j) rfl γ E hT
      (by convert AF using 1)
  have ht := P.uniformBoundaryCompatible_reindex (Option γ) β F hPF e.symm.toEmbedding
  change P.uniformBoundaryCompatible β (fun l => F (e.symm l)) at ht
  have heq : (fun l => F (e.symm l)) = D := by
    funext l
    exact (hF (e.symm l)).trans (congrArg D (e.apply_symm_apply l))
  rwa [heq] at ht

theorem terminal_order
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}} {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := LogarithmicProgram.Construction.DimensionLogarithmicProgram.terminal_order T

theorem exists_etaleComparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}} {X Y V W : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    {D : β → X.IdealSheafData} {E : β → V.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) W k M}
    (T : DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P)
    (S : DimensionAuxiliaryProgram 𝒮 j schedule V h L E W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  apply LogarithmicProgram.Construction.DimensionLogarithmicProgram.exists_etaleComparison T S q hstructure
  · rw [GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap, hJ, hD]
  · intro l
    exact hD l.val

end DimensionAuxiliaryProgram

end

section

/-! A scheduled auxiliary program has an exact incidence trace including its retained old boundary label. -/

def dimensionAuxiliaryIncidenceTrace {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d}
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (j : β)
    (schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β :=
  (LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace schedule).adjoinCarrier.reindex β
    (Equiv.optionSubtypeNe j).symm.toEmbedding

theorem dimensionAuxiliaryIncidenceTrace_length {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d}
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (j : β)
    (schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}) :
    (dimensionAuxiliaryIncidenceTrace j schedule).length = schedule.stepCount := by
  rw [dimensionAuxiliaryIncidenceTrace, Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.reindex_length,
    Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.adjoinCarrier_length, LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace_length]

theorem DimensionAuxiliaryProgram.stepCount
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P) :
    P.stepCount = schedule.stepCount := LogarithmicProgram.Construction.DimensionLogarithmicProgram.stepCount T

theorem DimensionAuxiliaryProgram.hasIncidenceTrace
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {j : β} {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j}} {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (T : DimensionAuxiliaryProgram 𝒮 j schedule X f J D Y g K P)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) :
    P.HasIncidenceTrace β D (dimensionAuxiliaryIncidenceTrace j schedule) := by
  classical
  let γ := {l : β // l ≠ j}
  let E : γ → X.IdealSheafData := fun l => D l.val
  have hT : P.HasIncidenceTrace γ E (LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace schedule) :=
    LogarithmicProgram.Construction.DimensionLogarithmicProgram.hasIncidenceTrace T
  let e : Option γ ≃ β := Equiv.optionSubtypeNe j
  let F : Option γ → X.IdealSheafData := fun l => match l with | none => D j | some s => E s
  have hF (l : Option γ) : F l = D (e l) := by cases l <;> rfl
  let AF : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f F [Finset.univ] :=
    A.pullbackLabels (fun l => some (e l))
      (fun l l' s hl hl' => e.injective (Option.some_injective _ (hl.trans hl'.symm))) F hF
  have hPF : P.HasIncidenceTrace (Option γ) F (LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace schedule).adjoinCarrier :=
    hT.adjoin_auxiliary_carrier (Nat.succ_pos n) P J (D j) rfl γ E _
      (by convert AF using 1)
  have ht := hPF.reindex P (Option γ) β F _ e.symm.toEmbedding
  change P.HasIncidenceTrace β (fun l => F (e.symm l)) (dimensionAuxiliaryIncidenceTrace j schedule) at ht
  have heq : (fun l => F (e.symm l)) = D := by
    funext l
    exact (hF (e.symm l)).trans (congrArg D (e.apply_symm_apply l))
  rwa [heq] at ht

end

section

/-! Dimension-indexed history schedules retain coefficient schedules and every intermediate boundary label type. -/

inductive DimensionHistorySchedule {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (n : ℕ) :
    {β γ : Type} → [Fintype β] → [Fintype γ] → [DecidableEq β] → (γ ↪ β) → Type 1
  | full {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (e : γ ↪ β)
      (he : Function.Surjective e) (ℓ : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n β) : DimensionHistorySchedule 𝒮 n e
  | clear {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] (e : γ ↪ β)
      (j : β) (hj : ∀ s, j ≠ e s) (ℓ : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j})
      (tail : DimensionHistorySchedule 𝒮 n
        (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory (ℓ.stepCount) e j hj)) :
      DimensionHistorySchedule 𝒮 n e

def DimensionHistorySchedule.stepCount {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
    {e : γ ↪ β} (S : Construction.DimensionHistorySchedule 𝒮 n e) : ℕ := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact ℓ.stepCount
  | @clear β γ _ _ _ e j hj ℓ tail ih => exact ℓ.stepCount + ih

end

section

/-! A dimension-indexed history program records auxiliary clearing, continuation on the boundary complement, and actual ambient extension. -/

inductive DimensionHistoryProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (n : ℕ) :
    {β γ : Type} → [Fintype β] → [Fintype γ] → [DecidableEq β] → {e : γ ↪ β} →
    Construction.DimensionHistorySchedule 𝒮 n e →
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K → Prop
  | full {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
      (e : γ ↪ β) (he : Function.Surjective e) (ℓ : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n β)
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
      {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
      (T : LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 ℓ X f J D Y g K P) :
      DimensionHistoryProgram 𝒮 n (.full e he ℓ) X f J D Y g K P
  | clear {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
      (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) (ℓ : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n {l : β // l ≠ j})
      (schedule : Construction.DimensionHistorySchedule 𝒮 n
        (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory (ℓ.stepCount) e j hj))
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J : X.IdealSheafData} {C J' : Y.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g C)
      (aux : DimensionAuxiliaryProgram 𝒮 j ℓ X f J D Y g C A)
      (hA : A.uniformBoundaryCompatible β D)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g J') (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (n + 1) (n + 1) A P)
      {V Z : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData} {M : Z.IdealSheafData}
      (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (A.transformedBoundaryComplement D j)
        ((A.transformedBoundaryComplement D j).ι ≫ g) (J'.comap (A.transformedBoundaryComplement D j).ι) V h L)
      (tail : DimensionHistoryProgram 𝒮 n schedule (A.transformedBoundaryComplement D j)
        ((A.transformedBoundaryComplement D j).ι ≫ g) (J'.comap (A.transformedBoundaryComplement D j).ι)
        (fun l => (A.boundaryAtLength D _ aux.stepCount l).comap (A.transformedBoundaryComplement D j).ι) V h L T)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) Y g J' Z k M) (r : V ⟶ Z)
      (comparison : R.EtaleComparison T (A.transformedBoundaryComplement D j).ι r)
      (hR : R.uniformBoundaryCompatible (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (ℓ.stepCount) β)
        (A.boundaryAtLength D _ aux.stepCount))
      (hcover : letI : Smooth k := R.endpoint_smooth
        ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M n).support : Set Z) ⊆ Set.range r) :
      DimensionHistoryProgram 𝒮 n (.clear e j hj ℓ schedule) X f J D Z k M (P.append R)

namespace DimensionHistoryProgram

theorem uniformBoundaryCompatible
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) : P.uniformBoundaryCompatible β D := by
  cases T with
  | full e he ℓ T => exact T.uniformBoundaryCompatible
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover =>
      have hP := same.uniformBoundaryCompatible _ _ hA
      have hcount := same.stepCount_eq.symm.trans aux.stepCount
      have hboundary := same.boundaryAtLength β D _ aux.stepCount hcount
      apply P.append_uniformBoundaryCompatible_fixed_labels R _ hP _ hcount
      rw [← hboundary]
      exact hR

theorem terminal_order
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  induction T with
  | full e he ℓ T => exact T.terminal_order
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      exact comparison.terminal_order_of_endpoint_cover R T _ r n hcover ih

theorem stepCount
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) : P.stepCount = schedule.stepCount := by
  induction T with
  | full e he ℓ T => exact T.stepCount
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      rw [Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_stepCount, ← same.stepCount_eq, aux.stepCount,
        comparison.stepCount_eq R T _ r, ih]
      rfl

end DimensionHistoryProgram

end

/-! Every complete dimension-indexed history program follows one pure incidence trace determined by the common schedule. -/

def DimensionHistorySchedule.incidenceTrace
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    (S : Construction.DimensionHistorySchedule 𝒮 n e) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace ℓ
  | @clear β γ _ _ _ e j hj ℓ tail ih =>
      exact (dimensionAuxiliaryIncidenceTrace j ℓ).appendAtLength
        ℓ.stepCount (dimensionAuxiliaryIncidenceTrace_length j ℓ) ih

theorem DimensionHistorySchedule.incidenceTrace_length
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    (S : Construction.DimensionHistorySchedule 𝒮 n e) : S.incidenceTrace.length = S.stepCount := by
  induction S with
  | @full β γ _ _ _ e he ℓ => exact LogarithmicProgram.Construction.dimensionLogarithmicIncidenceTrace_length ℓ
  | @clear β γ _ _ _ e j hj ℓ tail ih =>
      change ((dimensionAuxiliaryIncidenceTrace j ℓ).appendAtLength _ _ tail.incidenceTrace).length = _
      rw [Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length, ih]
      rfl

theorem DimensionHistoryProgram.hasIncidenceTrace
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) :
    P.HasIncidenceTrace β D schedule.incidenceTrace := by
  induction T with
  | full e he ℓ T => exact T.hasIncidenceTrace
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      let _ := A.endpoint_smooth
      have hAB := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible A _ hA
      obtain ⟨EA⟩ := A.boundaryCompatible_source_atlas _ hAB
      have htraceA := aux.hasIncidenceTrace EA
      obtain ⟨EY⟩ := A.boundaryAtLength_atlas _ hAB _ aux.stepCount
      have hclear := A.auxiliary_clearance (Nat.succ_pos n) _ _ rfl
        (by simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using aux.terminal_order)
      rw [same.transformIdeal] at hclear
      have htraceR := R.hasIncidenceTrace_of_order_neighborhood T _ r comparison
        (Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus _ _ _ (n + 1) hclear)
        _ _ EY _ ih
      exact same.append_traceAtLength A P R _ _ htraceA _ (dimensionAuxiliaryIncidenceTrace_length j ℓ) _ htraceR

end AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary.Construction

end

end OAI
