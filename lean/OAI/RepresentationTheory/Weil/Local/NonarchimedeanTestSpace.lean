import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # Nonarchimedean Test Space -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction

noncomputable section

/-! Locally constant test functions and actual quadratic lifts at nonarchimedean places. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem schwartzBruhat_totallyDisconnected_iff
    {k : Type} [NormedField k] [TotallyDisconnectedSpace k] {n : ℕ}
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} :
    f ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n ↔ IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨d, e, φ, rfl⟩
        · exact hf
        · have hs : IsPreconnected (Set.univ : Set (FunctionsMetaplectic.Construction.Position k n)) := by
            rw [← e.surjective.range_eq, ← Set.image_univ]
            exact isPreconnected_univ.image e e.continuous.continuousOn
          let : Subsingleton (FunctionsMetaplectic.Construction.Position k n) := Set.subsingleton_of_univ_subsingleton hs.subsingleton
          constructor
          · exact IsLocallyConstant.of_constant _
              (fun x y => congrArg (fun z => φ (e.symm z)) (Subsingleton.elim x y))
          · exact HasCompactSupport.of_compactSpace _
    | zero => exact ⟨IsLocallyConstant.const 0,
        HasCompactSupport.intro isCompact_empty (fun _ _ => rfl)⟩
    | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    | smul c f _ hf =>
        exact ⟨hf.1.comp (fun z => c * z), hf.2.smul_left⟩
  · exact fun hf => FunctionsMetaplectic.Construction.compact_locallyConstant_mem hf.1 hf.2

theorem nonarchimedean_character_locallyConstant
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k]
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) : IsLocallyConstant (fun t => ψ t) := by
  let χ := FourierTools.Construction.circleCharacter ψ hUnitary
  have hχ : Continuous χ := FourierTools.Construction.circleCharacter_continuous ψ hUnitary hContinuous
  have hzero : χ 0 ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [χ.map_zero_eq_one]
    exact ⟨0, by simpa using (half_pos Real.pi_pos), Circle.exp_zero⟩
  have hn : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) :=
    ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds hzero
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hn
  have hker (t : k) (ht : t ∈ U) : ψ t = 1 := by
    have h : χ t = 1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (fun m _ => by
      rw [← χ.map_nsmul_eq_pow]
      exact hU (U.nsmul_mem ht m))
    exact congrArg (fun z : Circle => (z : ℂ)) h
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hnh : ∀ᶠ y in 𝓝 t, y - t ∈ U := by
    exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using U.isOpen.mem_nhds U.zero_mem)
  filter_upwards [hnh] with y hy
  have hh := ψ.map_add_eq_mul (y - t) t
  simpa [hker (y - t) hy] using hh

theorem nonarchimedean_quadratic_mem
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t))
    (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := schwartzBruhat_totallyDisconnected_iff.mp f.property
  apply FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact ((nonarchimedean_character_locallyConstant ψ hUnitary hContinuous).comp_continuous
      (show Continuous (FunctionsMetaplectic.Construction.quadratic B) by unfold FunctionsMetaplectic.Construction.quadratic; fun_prop)).mul hf
  · exact hs.mul_left

/-- The quadratic generator over an ultrametric local field has the stated
bare-cover lift, without any representation or membership assumption. -/
def nonarchimedeanQuadraticMetaplectic
    {k : Type} [NormedField k] [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FunctionsMetaplectic.Construction.Metaplectic k n ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  exact QuadraticIntertwiner.Construction.quadraticMetaplectic ψ hUnitary
    (nonarchimedean_quadratic_mem ψ hUnitary hContinuous) B

theorem nonarchimedeanQuadraticMetaplectic_projection
    {k : Type} [NormedField k] [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FunctionsMetaplectic.Construction.metaplecticProjection k n ψ
      (nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hUnitary hContinuous B) =
        Generators.Construction.quadraticSymplectic B := rfl

theorem nonarchimedeanQuadraticMetaplectic_apply
    {k : Type} [NormedField k] [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hContinuous : Continuous (fun t => ψ t)) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (FunctionsMetaplectic.Construction.weilRepresentation k n ψ
      (nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hUnitary hContinuous B) f).val x =
        ψ (FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction
