import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.TraceResidualTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary

/-! # Residual Finite Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualFiniteExistence.Construction

noncomputable section

/-! Residual-order induction constructs one schedule for a finite family of surface problems at any positive control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_finite_surface_residual_programs (b : ℕ) (hb : 0 < b) (m : ℕ) :
    ∀ {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] (a : β → ℕ)
      (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
      (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J I : ∀ i, (X i).IdealSheafData),
      (∀ i, J i ≠ ⊥) → (∀ i, topologicalKrullDim (X i) ≤ 2) →
      ∀ (D : ∀ i, β → (X i).IdealSheafData) (_E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]),
      (∀ i, I i = Global.MixedBoundary.Construction.boundaryMonomialSheaf (D i) a * J i) →
      (∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) m = ⊤) →
      ∃ schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β a, ∀ i,
        ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
          (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (I i) Y g K),
          ResidualProgram.Construction.SurfaceResidualProgram b schedule (X i) (f i) (J i) (I i) (D i) Y g K P := by
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
        obtain ⟨S, hex⟩ := PositiveSurface.Construction.exists_finite_positive_surface_order_programs c hc X f C hC hd D E hCb
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
        have hdU (i : ι) : topologicalKrullDim (U i) ≤ 2 :=
          (U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans ((A i).endpoint_dimension_le 2 (hd i))
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
        obtain ⟨S, hex⟩ := PositiveSurface.Construction.exists_finite_positive_surface_order_programs (m + 1) (Nat.succ_pos m) X f J hJ hd D E hbound
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
        have hdY (i : ι) : topologicalKrullDim (Y i) ≤ 2 := (A i).endpoint_dimension_le 2 (hd i)
        have hbound' (i : ι) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (J' i) m = ⊤ := by
          simpa only [Nat.add_sub_cancel] using (order i).terminal_order
        obtain ⟨schedule, htail⟩ := ih a' Y g J' I' hJ' hdY D' EA (fun _ => rfl) hbound'
        choose Z h K R tail using htail
        exact ⟨.higher a hle S schedule, fun i => ⟨Z i, h i, K i, (P i).append (R i),
          .higher a hle S schedule (A i) (order i) (P i) (same i) (R i) (tail i)⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualFiniteExistence.Construction
