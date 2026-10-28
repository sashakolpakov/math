import OAI.RepresentationTheory.Weil.Local.BruhatCosets

/-! # Bare Generation -/

namespace OAI.RepresentationTheory.Weil.Local.BareGeneration.Construction

noncomputable section

/-! Concrete generators for the intrinsic nonarchimedean bare subgroup. -/

open scoped Classical commutatorElement

theorem central_conjugation {G : Type*} [Group G] {z x : G} (hz : Commute z x) :
    z * x * z⁻¹ = x := by rw [hz.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem commutator_le_of_central_kernel
    {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (H : Subgroup G)
    (hs : ∀ x : G, ∃ a ∈ H, π a = π x)
    (hk : ∀ z : G, π z = 1 → ∀ x : G, Commute z x) : commutator G ≤ H := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨a, b, rfl⟩
  obtain ⟨a', ha', hpa⟩ := hs a
  obtain ⟨b', hb', hpb⟩ := hs b
  let z := a * a'⁻¹
  let w := b * b'⁻¹
  have hz : ∀ x, Commute z x := hk z (by dsimp [z]; rw [map_mul, map_inv, hpa, mul_inv_cancel])
  have hw : ∀ x, Commute w x := hk w (by dsimp [w]; rw [map_mul, map_inv, hpb, mul_inv_cancel])
  have ha : a = z * a' := by dsimp [z]; group
  have hb : b = w * b' := by dsimp [w]; group
  have hcomm : ⁅a, b⁆ = ⁅a', b'⁆ := by
    rw [ha, hb, commutatorElement_mul_left_eq_conj_mul,
      (hz (w * b')).commutator_eq, mul_one, central_conjugation (hz _),
      commutatorElement_mul_right_eq_mul_conj, (hw a').symm.commutator_eq, one_mul,
      central_conjugation (hw _)]
  rw [hcomm, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha' hb') (H.inv_mem ha')) (H.inv_mem hb')

theorem nonarchimedean_oscillator_kernel_central
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (h : FunctionsMetaplectic.Construction.Oscillator k n ψ) : Commute g h := by
  obtain ⟨c, hs⟩ := BruhatCosets.Construction.nonarchimedean_oscillator_kernel_scalar hNondiscrete ψ hu hc hn g hg
  change g * h = h * g
  apply Subtype.ext
  apply Prod.ext
  · change g.val.1 * h.val.1 = h.val.1 * g.val.1
    have hg1 : g.val.1 = 1 := hg
    simp [hg1]
  · apply LinearEquiv.ext
    intro f
    change g.val.2 (h.val.2 f) = h.val.2 (g.val.2 f)
    rw [hs, hs, map_smul]

theorem subgroup_projection_surjective_of_quadratic_weyl
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (H : Subgroup (FunctionsMetaplectic.Construction.Oscillator k n ψ))
    (hU : ∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n, (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val ∈ H)
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : w ∈ H) (hwπ : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n) :
    H.map (OscillatorProjection.Construction.oscillatorProjection k n ψ) = ⊤ := by
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc ⟨-B.val, B.property.neg⟩
    refine ⟨w⁻¹ * u.val * w, H.mul_mem (H.mul_mem (H.inv_mem hw) (hU _)) hw, ?_⟩
    rw [map_mul, map_mul, map_inv, hwπ]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation k n B).symm
  · intro B
    exact ⟨(NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val, hU B, rfl⟩

theorem nonarchimedean_bare_subgroup_generated
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (w : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (hwπ : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ w = Generators.Construction.weylSymplectic k n) :
    FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ = Subgroup.closure
      (Set.range (fun B : FunctionsMetaplectic.Construction.SymmetricMatrix k n => (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val) ∪
        {w.val, FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) := by
  let H := Subgroup.closure
    (Set.range (fun B : FunctionsMetaplectic.Construction.SymmetricMatrix k n => (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val) ∪
      {w.val, FunctionsMetaplectic.Construction.oscillatorMinus k n ψ})
  have hU (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val ∈ H :=
    Subgroup.subset_closure (Or.inl ⟨B, rfl⟩)
  have hw : w.val ∈ H := Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))
  have hm : FunctionsMetaplectic.Construction.oscillatorMinus k n ψ ∈ H := Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  have hsurj := subgroup_projection_surjective_of_quadratic_weyl hNondiscrete ψ hu hc H hU w.val hw hwπ
  have hder : commutator (FunctionsMetaplectic.Construction.Oscillator k n ψ) ≤ H :=
    commutator_le_of_central_kernel (OscillatorProjection.Construction.oscillatorProjection k n ψ) H
      (fun x => by
        have h : OscillatorProjection.Construction.oscillatorProjection k n ψ x ∈ H.map (OscillatorProjection.Construction.oscillatorProjection k n ψ) := by rw [hsurj]; trivial
        exact h)
      (nonarchimedean_oscillator_kernel_central hNondiscrete ψ hu hc hn)
  apply le_antisymm
  · change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) ≤ H
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · apply hder
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ hm
  · change H ≤ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ
    rw [show H = Subgroup.closure _ from rfl, Subgroup.closure_le]
    intro x hx
    rcases hx with ⟨B, rfl⟩ | hx
    · exact (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).property
    · rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact w.property
      · exact (Set.mem_singleton_iff.mp hx) ▸ (FunctionsMetaplectic.Construction.metaplecticMinus k n ψ).property

end

end OAI.RepresentationTheory.Weil.Local.BareGeneration.Construction
