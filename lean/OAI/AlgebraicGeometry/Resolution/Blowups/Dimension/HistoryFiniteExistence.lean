import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionAuxiliaryPrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlPrefixOpenExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.TransformNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary

/-! # History Finite Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryFiniteExistence.Construction

noncomputable section

section

/-! Finite families in the next dimension have one common boundary-history schedule and actual full-boundary programs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_finite_dimension_history_programs_of_count {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (n k : ℕ) :
    ∀ {β γ ι : Type} [Fintype β] [Fintype γ] [DecidableEq β] [Fintype ι]
      (e : γ ↪ β), Fintype.card β - Fintype.card γ ≤ k →
      ∀ (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
        (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData),
      (∀ i, J i ≠ ⊥) → (∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ)) →
      ∀ (D : ∀ i, β → (X i).IdealSheafData)
        (_E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
        (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i)),
      (∀ i, ((G i).reindex e).logarithmicIdeal (J i) (n + 1) = ⊤) →
      ∃ schedule : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 n e, ∀ i,
        ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
          (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
          HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule (X i) (f i) (J i) (D i) Y g K P := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro β γ ι _ _ _ _ e hcount X _ _ _ f _ J hJ hd D E G hbound
      by_cases he : Function.Surjective e
      · have hfull (i : ι) : (G i).logarithmicIdeal (J i) (n + 1) = ⊤ := by
          have hi := hbound i
          rwa [(G i).logarithmicIdeal_surjective_reindex e he (J i) (n + 1)] at hi
        obtain ⟨ℓ, hprogram⟩ := Finite.DimensionLogarithmicPrograms.Construction.exists_finite_dimension_logarithmic_programs 𝒮 n X f J hJ hd D E G hfull
        choose Y g K P hP using hprogram
        exact ⟨.full e he ℓ, fun i => ⟨Y i, g i, K i, P i, .full e he ℓ (hP i)⟩⟩
      · have hex : ∃ j : β, ∀ s : γ, j ≠ e s := by
          by_contra! hall
          exact he (fun j => by obtain ⟨s, hs⟩ := hall j; exact ⟨s, hs.symm⟩)
        obtain ⟨j, hj⟩ := hex
        obtain ⟨ℓ, hprogram⟩ := Finite.DimensionAuxiliaryPrograms.Construction.exists_finite_dimension_auxiliary_programs 𝒮 n X f J hJ hd D E j
        choose Y g C A aux using hprogram
        let N := ℓ.stepCount
        have hA (i : ι) : (A i).uniformBoundaryCompatible β (D i) := (aux i).uniformBoundaryCompatible (E i)
        have hAB (i : ι) : (A i).boundaryCompatible β (D i) :=
          Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible (A i) (D i) (hA i)
        choose J' H' P Hprefix same sameH haux using fun i =>
          (A i).exists_auxiliary_same_blowups (Nat.succ_pos n) (J i) (D i j) rfl
        let : ∀ i, Smooth (g i) := fun i => (A i).endpoint_smooth
        let : ∀ i, IsIntegral (Y i) := fun i => (A i).endpoint_integral
        let : ∀ i, IsLocallyNoetherian (Y i) := fun i => LocallyOfFiniteType.isLocallyNoetherian (g i)
        let : ∀ i, CompactSpace (Y i) := fun i => QuasiCompact.compactSpace_of_compactSpace (A i).toBase
        let : ∀ i, IsNoetherian (Y i) := fun _ => ⟨⟩
        let U (i : ι) := (A i).transformedBoundaryComplement (D i) j
        let : ∀ i, Nonempty (U i) := fun i => by
          obtain ⟨x, hx⟩ := GlobalBlowup.Local.Construction.idealSheaf_supportComplement_nonempty ((A i).transformIdeal (D i j) 1)
            ((A i).transformIdeal_ne_bot _ _ ((E i).component_ne_bot j))
          exact ⟨⟨x, hx⟩⟩
        let : ∀ i, IsIntegral (U i) := fun i => isIntegral_of_isOpenImmersion (U i).ι
        let : ∀ i, IsLocallyNoetherian (U i) := fun i => LocallyOfFiniteType.isLocallyNoetherian (U i).ι
        let : ∀ i, NoetherianSpace (U i) := fun i => (U i).ι.isOpenEmbedding.isInducing.noetherianSpace
        let DU (i : ι) (l : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) :=
          ((A i).boundaryAtLength (D i) N (aux i).stepCount l).comap (U i).ι
        let EA (i : ι) := Classical.choice ((A i).boundaryAtLength_atlas (D i) (hAB i) N (aux i).stepCount)
        let EU (i : ι) := (EA i).comapOpen (g i) (U i).ι
        have hexG (i : ι) : ∃ B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas ((U i).ι ≫ g i) (DU i),
            (B.reindex (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory N e j hj)).logarithmicIdeal ((J' i).comap (U i).ι) (n + 1) = ⊤ := by
          obtain ⟨B, hB⟩ := (A i).exists_fixed_length_extended_history_on_complement
            (D i) (G i) e j hj (J i) (hbound i) (hAB i) N (aux i).stepCount
          rw [(same i).transformIdeal] at hB
          exact ⟨B, hB⟩
        choose GU hGU using hexG
        have hJ' (i : ι) : J' i ≠ ⊥ := (P i).endpoint_ideal_ne_bot (hJ i)
        have hJU (i : ι) : (J' i).comap (U i).ι ≠ ⊥ :=
          Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot (U i).ι (J' i) (hJ' i)
        have hdU (i : ι) : topologicalKrullDim (U i) ≤ (d + 1 : ℕ) :=
          (U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans ((A i).endpoint_dimension_le (d + 1) (hd i))
        have hlt : Fintype.card (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β) - Fintype.card (Option (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N γ)) < k :=
          (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory_missing_count_lt N e j hj).trans_le hcount
        obtain ⟨schedule, htail⟩ := ih _ hlt (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory N e j hj) le_rfl
          (fun i => (U i).toScheme) (fun i => (U i).ι ≫ g i) (fun i => (J' i).comap (U i).ι)
          hJU hdU DU EU GU hGU
        choose V h L T tail using htail
        have hcover (i : ι) : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (J' i) n).support : Set (Y i)) ⊆ Set.range (U i).ι := by
          have hclear := (A i).auxiliary_clearance (Nat.succ_pos n) (J i) (D i j) rfl
            (by simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using (aux i).terminal_order)
          rw [(same i).transformIdeal] at hclear
          exact Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus
            (g i) (J' i) ((A i).transformIdeal (D i j) 1) (n + 1) hclear
        choose Z k M R r hR comparison hopen hremaining using fun i =>
          (T i).exists_uniform_extension_from_order_neighborhood (Y i) (g i) (J' i) (hJ' i) (U i).ι rfl rfl
            (by simpa only [Nat.add_sub_cancel] using hcover i) (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)
            ((A i).boundaryAtLength (D i) N (aux i).stepCount) (EA i) (tail i).uniformBoundaryCompatible
        refine ⟨.clear e j hj ℓ schedule, ?_⟩
        intro i
        exact ⟨Z i, k i, M i, (P i).append (R i), .clear e j hj ℓ schedule (A i) (aux i) (hA i)
          (P i) (same i) (T i) (tail i) (R i) (r i) (comparison i) (hR i)
          (by simpa only [Nat.add_sub_cancel] using hremaining i)⟩

end

/-! Ordinary maximum-order problems in the next dimension in a finite family have one common complete history schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_dimension_history_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β γ ι : Type} [Fintype β] [Fintype γ] [DecidableEq β] [Fintype ι] (e : γ ↪ β)
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i))
    (hbound : ∀ i, ((G i).reindex e).logarithmicIdeal (J i) (n + 1) = ⊤) :
    ∃ schedule : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 n e, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule (X i) (f i) (J i) (D i) Y g K P :=
  exists_finite_dimension_history_programs_of_count 𝒮 n (Fintype.card β - Fintype.card γ) e le_rfl
    X f J hJ hd D E G hbound

theorem exists_finite_dimension_order_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (hbound : ∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) (n + 1) = ⊤) :
    ∃ schedule : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 n (Function.Embedding.ofIsEmpty : Fin 0 ↪ β), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule (X i) (f i) (J i) (D i) Y g K P := by
  classical
  let G (i : ι) := Classical.choice (E i).exists_modelAtlas
  apply exists_finite_dimension_history_programs 𝒮 n Function.Embedding.ofIsEmpty X f J hJ hd D E G
  intro i
  rw [GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_empty]
  exact hbound i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryFiniteExistence.Construction
