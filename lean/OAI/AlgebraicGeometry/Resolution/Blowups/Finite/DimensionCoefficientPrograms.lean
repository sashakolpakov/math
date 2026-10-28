import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasPrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.TerminalIncidenceTraceProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.IntegralNormalChartCover
import OAI.AlgebraicGeometry.Resolution.Blowups.NormalChartCoefficientNonzero
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceCoefficientPersistence

/-! # Dimension Coefficient Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionCoefficientPrograms.Construction

noncomputable section

/-! A finite bounded family in the next dimension has one shared coefficient schedule, including terminal family members. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_bounded_dimension_coefficient_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β τ : Type} [Fintype β] [DecidableEq β] [Fintype τ]
    (X : τ → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData) (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i))
    (hlog : ∀ i, (G i).logarithmicIdeal (J i) (n + 1) = ⊤)
    (A : ∀ i, GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (f i) (J i) n) (bound : τ → ℕ)
    (hbound : ∀ i a, ((A i).choice a).HasBound (bound i)) :
    ∃ schedule : 𝒮.Schedule (n + 1).factorial β, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        Dimension.CoefficientProgram.Construction.DimensionCoefficientProgram 𝒮 schedule (f i) (J i) (D i) P := by
  classical
  let σ := {i : τ // Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) n ≠ ⊤}
  choose s C hR hH hcover using fun i : σ =>
    IntegralNormalChartCover.Construction.exists_finite_integral_global_normal_chart_cover (G i.val) (J i.val) n (hlog i.val)
  let κ (i : σ) := ↥(s i)
  let : ∀ i, Fintype (κ i) := fun _ => inferInstance
  let : ∀ i, Nonempty (κ i) := fun i => by
    have hne : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i.val) (J i.val) n).support : Set (X i.val)).Nonempty := by
      by_contra hn
      apply i.property
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      apply SetLike.coe_injective
      exact Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := hne
    obtain ⟨a, _, _⟩ := hcover i x hx
    exact ⟨a⟩
  let : ∀ (i : σ) (a : κ i), IsDomain (C i a).chart.ring := hR
  let : ∀ (i : σ) (a : κ i), IsIntegral (C i a).chart.nativeCarrier.subscheme := hH
  have hC (i : σ) (a : κ i) : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf ((C i a).chart.map ≫ f i.val)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (f i.val) (J i.val) n).comap (C i a).chart.map) (n + 1)
        (C i a).chart.nativeCarrier.subschemeι ≠ ⊥ := by
    rw [Global.SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr ((C i a).chart.map ≫ f i.val)
      (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C i a).chart.ring) (C i a).chart.ground, (C i a).chart.homogenized_restrict]
    exact (C i a).chart.native_coefficient_ne_bot_of_atlas_bound a.val.property
      (A i.val) (bound i.val) (hbound i.val)
  obtain ⟨schedule, hprograms⟩ := Modeled.UniformCarrierAtlasPrograms.Construction.exists_finite_modeled_uniform_carrier_atlas_programs 𝒮 n
    (fun i : σ => X i.val) (fun i => f i.val) (fun i => J i.val) (fun i => hJ i.val) (fun i => hd i.val)
    (fun i => D i.val) (fun i => E i.val) κ (fun _ a => a.val.val) C hcover hC
  refine ⟨schedule, ?_⟩
  intro i
  by_cases ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) n = ⊤
  · obtain ⟨Y, g, K, P, htrace, hterm⟩ := TerminalIncidenceTraceProgram.Construction.exists_terminal_program_with_incidence_trace
      (n + 1) (Nat.succ_pos n) (𝒮.incidenceTrace schedule) (X i) (f i) (J i) (D i) (E i)
      (by simpa only [Nat.add_sub_cancel] using ht)
    exact ⟨Y, g, K, P, htrace, by simpa only [Nat.add_sub_cancel] using hterm, Or.inl ht⟩
  · obtain ⟨Y, g, K, P, ⟨certificate⟩⟩ := hprograms ⟨i, ht⟩
    obtain ⟨L, Q, same, hterm⟩ := P.exists_homogenized_interval_terminal_prefix
      (J i) (Global.Homogenization.Construction.le_smoothHomogenizedIdealSheaf (f i) (J i) n) le_rfl certificate.terminal
    exact ⟨Y, g, L, Q, same.hasIncidenceTrace (D i) (𝒮.incidenceTrace schedule) certificate.trace,
      hterm, Or.inr ⟨K, P, ⟨certificate⟩, same⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionCoefficientPrograms.Construction
