import OAI.AlgebraicGeometry.Resolution.Blowups.PositiveDimensionHas
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceExponents
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.TraceCompanionResidualDrop
import OAI.AlgebraicGeometry.Resolution.Blowups.TraceResidualTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialOrderBound

/-! # Residual Finite -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.ResidualFinite.Construction

noncomputable section

section

/-! Residual-order schedules share every coefficient level, incidence trace, and monomial exponent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive DimensionResidualSchedule {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (b : ℕ) :
    (m : ℕ) → (β : Type) → [Fintype β] → [DecidableEq β] → (β → ℕ) → Type 1
  | monomial {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ)
      (S : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a [Finset.univ]) : DimensionResidualSchedule 𝒮 b 0 β a
  | higher {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hle : b ≤ m + 1)
      (S : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 m (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (tail : DimensionResidualSchedule 𝒮 b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.residualExponents a (m + 1) b)) : DimensionResidualSchedule 𝒮 b (m + 1) β a
  | companion {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hlt : m + 1 < b)
      (S : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 ((m + 1) * (b - (m + 1)) - 1)
        (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (tail : DimensionResidualSchedule 𝒮 b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.companionExponents a (m + 1) b)) : DimensionResidualSchedule 𝒮 b (m + 1) β a

def DimensionResidualSchedule.incidenceTrace {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} (S : Construction.DimensionResidualSchedule 𝒮 b m β a) : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction S with
  | monomial a S => exact S.incidenceTrace
  | higher a hle S tail ih => exact S.incidenceTrace.append ih
  | companion a hlt S tail ih => exact S.incidenceTrace.append ih

end

section

/-! Recorded residual programs combine exact changes of control with continuation on a residual-order neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive DimensionResidualProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (b : ℕ) :
    {m : ℕ} → {β : Type} → [Fintype β] → [DecidableEq β] → {a : β → ℕ} →
    Construction.DimensionResidualSchedule 𝒮 b m β a →
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J I : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K → Prop
  | monomial {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ)
      (S : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a [Finset.univ])
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
      {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
      (H : Boundary.MonomialProgram.Construction.BoundaryMonomialProgram b β a [Finset.univ] S X f I D Y g K P) :
      DimensionResidualProgram 𝒮 b (.monomial a S) X f J I D Y g K P
  | higher {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hle : b ≤ m + 1)
      (S : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 m (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (schedule : Construction.DimensionResidualSchedule 𝒮 b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.residualExponents a (m + 1) b))
      {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J I : X.IdealSheafData} {J' I' : Y.IdealSheafData} {K : Z.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m + 1) X f J Y g J')
      (order : PositiveDimensionHas.Construction.PositiveDimensionOrderProgram 𝒮 (m + 1) β S X f J D Y g J' A)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g I') (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m + 1) b A P)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b Y g I' Z h K)
      (tail : DimensionResidualProgram 𝒮 b schedule Y g J' I'
        (A.boundaryAtLength D S.incidenceTrace.length (order.hasIncidenceTrace.stepCount A D S.incidenceTrace)) Z h K R) :
      DimensionResidualProgram 𝒮 b (.higher a hle S schedule) X f J I D Z h K (P.append R)
  | companion {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] (a : β → ℕ) (hlt : m + 1 < b)
      (S : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 ((m + 1) * (b - (m + 1)) - 1)
        (Function.Embedding.ofIsEmpty : Fin 0 ↪ β))
      (schedule : Construction.DimensionResidualSchedule 𝒮 b m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
        (S.incidenceTrace.companionExponents a (m + 1) b))
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth g]
      {J I : X.IdealSheafData} {C J' I' : Y.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix ((m + 1) * (b - (m + 1))) X f
        (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b) Y g C)
      (order : PositiveDimensionHas.Construction.PositiveDimensionOrderProgram 𝒮 ((m + 1) * (b - (m + 1))) β S X f
        (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b) D Y g C A)
      (B : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m + 1) X f J Y g J')
      (sameB : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups ((m + 1) * (b - (m + 1))) (m + 1) A B)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g I')
      (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups ((m + 1) * (b - (m + 1))) b A P)
      {V Z : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData} {M : Z.IdealSheafData}
      (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1))
        ((Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι ≫ g) (I'.comap (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι) V h L)
      (tail : DimensionResidualProgram 𝒮 b schedule (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1))
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
      DimensionResidualProgram 𝒮 b (.companion a hlt S schedule) X f J I D Z k M (P.append R)

namespace DimensionResidualProgram

theorem terminal_order {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} (hb : 0 < b) {m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : Construction.DimensionResidualSchedule 𝒮 b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.DimensionResidualProgram 𝒮 b schedule X f J I D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  induction H with
  | monomial a S H => exact H.terminal_order hb
  | higher a hle S schedule A order P same R tail ih => exact ih
  | companion a hlt S schedule A order B sameB P same T tail R r comparison hstart hcover ih =>
      exact comparison.terminal_order_of_endpoint_cover R T _ r (b - 1) hcover ih

theorem hasIncidenceTrace {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : Construction.DimensionResidualSchedule 𝒮 b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.DimensionResidualProgram 𝒮 b schedule X f J I D Y g K P) :
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

theorem uniformBoundaryCompatible {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : Construction.DimensionResidualSchedule 𝒮 b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : Construction.DimensionResidualProgram 𝒮 b schedule X f J I D Y g K P) : P.uniformBoundaryCompatible β D :=
  H.hasIncidenceTrace.uniformBoundaryCompatible P D schedule.incidenceTrace

end DimensionResidualProgram

end

section

/-! Residual-order induction constructs one schedule for a finite family of problems in the next dimension at any positive control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_finite_dimension_residual_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (b : ℕ) (hb : 0 < b) (m : ℕ) :
    ∀ {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] (a : β → ℕ)
      (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
      (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J I : ∀ i, (X i).IdealSheafData),
      (∀ i, J i ≠ ⊥) → (∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ)) →
      ∀ (D : ∀ i, β → (X i).IdealSheafData) (_E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]),
      (∀ i, I i = Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a * J i) →
      (∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) m = ⊤) →
      ∃ schedule : Construction.DimensionResidualSchedule 𝒮 b m β a, ∀ i,
        ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
          (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (I i) Y g K),
          Construction.DimensionResidualProgram 𝒮 b schedule (X i) (f i) (J i) (I i) (D i) Y g K P := by
  classical
  induction m with
  | zero =>
      intro β ι _ _ _ a X _ _ _ f _ J I hJ hd D E hI hbound
      obtain ⟨S⟩ := Boundary.MonomialSchedule.Construction.exists_boundary_monomial_schedule b hb (Fintype.card β) β a [Finset.univ]
        (by intro S hS; exact List.mem_singleton.mp hS ▸ le_rfl)
      refine ⟨.monomial a S, ?_⟩
      intro i
      have hmono : I i = Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a := by
        have ht : J i = ⊤ := by simpa only [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] using hbound i
        rw [hI i, ht, ← Scheme.IdealSheafData.one_eq_top, mul_one]
      obtain ⟨Y, g, K, P, hP⟩ := S.exists_program hb (X i) (f i) (D i) (I i) hmono (E i).component_ne_bot (E i)
      exact ⟨Y, g, K, P, .monomial a S hP⟩
  | succ m ih =>
      intro β ι _ _ _ a X _ _ _ f _ J I hJ hd D E hI hbound
      have hIfun : I = fun i => Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a * J i := funext hI
      subst I
      by_cases hlt : m + 1 < b
      · let c := (m + 1) * (b - (m + 1))
        have hc : 0 < c := Nat.mul_pos (Nat.succ_pos m) (by omega)
        let C (i : ι) := Global.CompanionIdeal.Construction.globalCompanionIdeal (J i) (Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a) (m + 1) b
        have hC (i : ι) : C i ≠ ⊥ := by
          intro hz
          have hle : J i ^ (b - (m + 1)) ≤ C i := le_sup_left
          rw [hz] at hle
          exact Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot (J i) (hJ i) _ (le_bot_iff.mp hle)
        have hCb (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (C i) c = ⊤ :=
          Global.CompanionIdeal.Construction.globalCompanionIdeal_differential_bound (f i) (J i) (Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a) (m + 1) b hlt (hbound i)
        obtain ⟨S, hex⟩ := PositiveDimensionHas.Construction.exists_finite_positive_dimension_order_programs 𝒮 c hc X f C hC hd D E hCb
        choose Y g K A order using hex
        have hA (i : ι) := (order i).hasIncidenceTrace
        let N := S.incidenceTrace.length
        let D' (i : ι) := (A i).boundaryAtLength (D i) N ((hA i).stepCount (A i) (D i) S.incidenceTrace)
        let a' := S.incidenceTrace.companionExponents a (m + 1) b
        let J' (i : ι) := (A i).transformIdeal (J i) (m + 1)
        let I' (i : ι) := Global.MixedBoundary.Construction.boundaryMonomialSheaf (D' i) a' * J' i
        choose B P sameB same using fun i =>
          (hA i).exists_companion_prefix (Nat.succ_pos m) hlt (A i) (D i) S.incidenceTrace (J i) a rfl
        let : ∀ i, Smooth (g i) := fun i => (A i).endpoint_smooth
        let : ∀ i, IsIntegral (Y i) := fun i => (A i).endpoint_integral
        let : ∀ i, IsLocallyNoetherian (Y i) := fun i => LocallyOfFiniteType.isLocallyNoetherian (g i)
        let : ∀ i, CompactSpace (Y i) := fun i => QuasiCompact.compactSpace_of_compactSpace (A i).toBase
        let : ∀ i, IsNoetherian (Y i) := fun _ => ⟨⟩
        have hJ' (i : ι) : J' i ≠ ⊥ := (B i).endpoint_ideal_ne_bot (hJ i)
        have hI' (i : ι) : I' i ≠ ⊥ := (P i).endpoint_ideal_ne_bot
          (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot _ _ (Integral.CenterSequenceReplacement.Construction.boundaryMonomialSheaf_ne_bot (D i) a (E i).component_ne_bot) (hJ i))
        let U (i : ι) := Global.ResidualNeighborhood.Construction.residualOrderDropOpen (g i) (J' i) (m + 1)
        let : ∀ i, IsIntegral (U i) := fun i => Global.ResidualNeighborhood.Construction.residualOrderDropOpen_integral (g i) (J' i) (hJ' i) (m + 1)
        let : ∀ i, IsLocallyNoetherian (U i) := fun i => LocallyOfFiniteType.isLocallyNoetherian (U i).ι
        let : ∀ i, NoetherianSpace (U i) := fun i => (U i).ι.isOpenEmbedding.isInducing.noetherianSpace
        let DU (i : ι) (l : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) := (D' i l).comap (U i).ι
        let EA (i : ι) := Classical.choice ((A i).boundaryAtLength_atlas (D i)
          (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible (A i) (D i)
            ((hA i).uniformBoundaryCompatible (A i) (D i) S.incidenceTrace)) N
          ((hA i).stepCount (A i) (D i) S.incidenceTrace))
        let EU (i : ι) := (EA i).comapOpen (g i) (U i).ι
        have hJU (i : ι) : (J' i).comap (U i).ι ≠ ⊥ := Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot (U i).ι _ (hJ' i)
        have hdU (i : ι) : topologicalKrullDim (U i) ≤ (d + 1 : ℕ) :=
          (U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans ((A i).endpoint_dimension_le (d + 1) (hd i))
        have hIU (i : ι) : (I' i).comap (U i).ι = Global.MixedBoundary.Construction.boundaryMonomialSheaf (DU i) a' * (J' i).comap (U i).ι := by
          rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, Global.MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
        have hboundU (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((U i).ι ≫ g i) ((J' i).comap (U i).ι) m = ⊤ := by
          simpa only [Nat.add_sub_cancel] using Global.ResidualNeighborhood.Construction.residualOrderDropOpen_residual_bound (g i) (J' i) (m + 1)
        obtain ⟨schedule, htail⟩ := ih a' (fun i => (U i).toScheme) (fun i => (U i).ι ≫ g i)
          (fun i => (J' i).comap (U i).ι) (fun i => (I' i).comap (U i).ι) hJU hdU DU EU hIU hboundU
        choose V h L T tail using htail
        have hstart (i : ι) : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (I' i) (b - 1)).support : Set (Y i)) ⊆ Set.range (U i).ι := by
          have hdrop := ((hA i).companion_residual_drop (Nat.succ_pos m) hlt (A i) (D i) S.incidenceTrace
            (J i) a rfl (hbound i) (order i).terminal_order).2
          exact Global.ResidualNeighborhood.Construction.residualOrderDropOpen_contains_order_support (g i) (Global.MixedBoundary.Construction.boundaryMonomialSheaf (D' i) a') (J' i) (m + 1) b hdrop
        choose Z k M R r hR comparison hopen hremaining using fun i =>
          (T i).exists_uniform_extension_from_order_neighborhood (Y i) (g i) (I' i) (hI' i) (U i).ι rfl rfl
            (hstart i) (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) (D' i) (EA i) (tail i).uniformBoundaryCompatible
        exact ⟨.companion a hlt S schedule, fun i => ⟨Z i, k i, M i, (P i).append (R i),
          .companion a hlt S schedule (A i) (order i) (B i) (sameB i) (P i) (same i)
            (T i) (tail i) (R i) (r i) (comparison i) (hstart i) (hremaining i)⟩⟩
      · have hle : b ≤ m + 1 := Nat.le_of_not_gt hlt
        obtain ⟨S, hex⟩ := PositiveDimensionHas.Construction.exists_finite_positive_dimension_order_programs 𝒮 (m + 1) (Nat.succ_pos m) X f J hJ hd D E hbound
        choose Y g J' A order using hex
        have hA (i : ι) := (order i).hasIncidenceTrace
        let N := S.incidenceTrace.length
        let D' (i : ι) := (A i).boundaryAtLength (D i) N ((hA i).stepCount (A i) (D i) S.incidenceTrace)
        let a' := S.incidenceTrace.residualExponents a (m + 1) b
        let I' (i : ι) := Global.MixedBoundary.Construction.boundaryMonomialSheaf (D' i) a' * J' i
        choose P same using fun i => (hA i).exists_lower_control_prefix (A i) b hb hle (D i) S.incidenceTrace a
        let : ∀ i, Smooth (g i) := fun i => (A i).endpoint_smooth
        let : ∀ i, IsIntegral (Y i) := fun i => (A i).endpoint_integral
        let : ∀ i, IsLocallyNoetherian (Y i) := fun i => LocallyOfFiniteType.isLocallyNoetherian (g i)
        let : ∀ i, CompactSpace (Y i) := fun i => QuasiCompact.compactSpace_of_compactSpace (A i).toBase
        let EA (i : ι) := Classical.choice ((A i).boundaryAtLength_atlas (D i)
          (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible (A i) (D i)
            ((hA i).uniformBoundaryCompatible (A i) (D i) S.incidenceTrace)) N
          ((hA i).stepCount (A i) (D i) S.incidenceTrace))
        have hJ' (i : ι) : J' i ≠ ⊥ := (A i).endpoint_ideal_ne_bot (hJ i)
        have hdY (i : ι) : topologicalKrullDim (Y i) ≤ (d + 1 : ℕ) := (A i).endpoint_dimension_le (d + 1) (hd i)
        have hbound' (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (J' i) m = ⊤ := by
          simpa only [Nat.add_sub_cancel] using (order i).terminal_order
        obtain ⟨schedule, htail⟩ := ih a' Y g J' I' hJ' hdY D' EA (fun _ => rfl) hbound'
        choose Z h K R tail using htail
        exact ⟨.higher a hle S schedule, fun i => ⟨Z i, h i, K i, (P i).append (R i),
          .higher a hle S schedule (A i) (order i) (P i) (same i) (R i) (tail i)⟩⟩

end

/-! Every finite family of nonzero ideals in the next dimension has common full-boundary programs at an arbitrary positive control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_dimension_control_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (b : ℕ) (hb : 0 < b) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]) :
    ∃ (m : ℕ) (schedule : Construction.DimensionResidualSchedule 𝒮 b m β (fun _ => 0)), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K),
        Construction.DimensionResidualProgram 𝒮 b schedule (X i) (f i) (J i) (J i) (D i) Y g K P := by
  classical
  choose bounds hbounds using fun i => Global.DifferentialOrderBound.Construction.exists_global_complex_differential_order_bound (f i) (J i) (hJ i)
  let m := Finset.univ.sup bounds
  have hbound (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) m = ⊤ :=
    Global.DifferentialFiltration.Construction.smoothDifferentialIdealSheaf_top_of_le (f i) (J i) (Finset.le_sup (Finset.mem_univ i)) (hbounds i)
  obtain ⟨schedule, hprogram⟩ := exists_finite_dimension_residual_programs 𝒮 b hb m (fun _ : β => 0)
    X f J J hJ hd D E (fun i => by simp only [Global.MixedBoundary.Construction.boundaryMonomialSheaf, pow_zero, Finset.prod_const_one, one_mul]) hbound
  exact ⟨m, schedule, hprogram⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.ResidualFinite.Construction
