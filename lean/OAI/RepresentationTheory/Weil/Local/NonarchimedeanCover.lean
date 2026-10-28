import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm
import OAI.RepresentationTheory.Weil.Local.RealCover

/-! # Nonarchimedean Cover -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction

noncomputable section

/-! Surjectivity of the actual bare metaplectic projection over ultrametric local fields. -/

open _root_.MeasureTheory

theorem exists_nonarchimedean_fourier_oscillator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Oscillator k n ψ, OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  obtain ⟨a, T, _, hT, hunitary⟩ :=
    NonarchimedeanFourier.Construction.exists_nonarchimedean_unitary_fourier hNondiscrete n ψ hu hc hn μ
  exact ⟨⟨(Generators.Construction.weylSymplectic k n, T), ⟨hunitary,
    NonarchimedeanFourier.Construction.scalar_fourier_intertwines hNondiscrete ψ hu hc μ (a : ℂ) T hT⟩⟩, rfl⟩

theorem ultrametric_metaplecticProjection_surjective
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) := by
  obtain ⟨w, hw⟩ := exists_nonarchimedean_fourier_oscillator hNondiscrete n ψ hu hc hn
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc ⟨-B.val, B.property.neg⟩
    have h : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
      have hh := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal).conj_mem
        u.val u.property w⁻¹
      simpa only [inv_inv] using hh
    refine ⟨⟨w⁻¹ * u.val * w, h⟩, ?_⟩
    change OscillatorProjection.Construction.oscillatorProjection k n ψ (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic B
    rw [map_mul, map_mul, map_inv, hw]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation k n B).symm
  · intro B
    exact ⟨NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B, rfl⟩

theorem nonarchimedean_metaplecticProjection_surjective
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  exact ultrametric_metaplecticProjection_surjective hNondiscrete n ψ hu hc hn

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction
