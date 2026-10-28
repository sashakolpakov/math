import OAI.RepresentationTheory.Weil.Local.QuarterTurnStructure
import OAI.RepresentationTheory.Weil.Local.BareGeneration
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Quarter Turn Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.QuarterTurnKernel.Construction

noncomputable section

/-! Bare-kernel signs in the nonarchimedean case when -1 is a square. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

def quarterTurnSubgroup {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ψ : AddChar k ℂ) (r : k) (hr : r ^ 2 = -1) :
    Subgroup (FunctionsMetaplectic.Construction.Oscillator k n ψ) where
  carrier := {a | ∀ f, a.val.2 (QuarterTurnStructure.Construction.quarterTurnStructure r hr f) = QuarterTurnStructure.Construction.quarterTurnStructure r hr (a.val.2 f)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb f
    change a.val.2 (b.val.2 (QuarterTurnStructure.Construction.quarterTurnStructure r hr f)) = QuarterTurnStructure.Construction.quarterTurnStructure r hr (a.val.2 (b.val.2 f))
    rw [hb, ha]
  inv_mem' := by
    intro a ha f
    change a.val.2.symm (QuarterTurnStructure.Construction.quarterTurnStructure r hr f) = QuarterTurnStructure.Construction.quarterTurnStructure r hr (a.val.2.symm f)
    apply a.val.2.injective
    rw [LinearEquiv.apply_symm_apply, ha, LinearEquiv.apply_symm_apply]

theorem nonarchimedean_metaplectic_le_quarterTurnSubgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (r : k) (hr : r ^ 2 = -1) :
    FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ ≤ quarterTurnSubgroup n ψ r hr := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let H := quarterTurnSubgroup n ψ r hr
  obtain ⟨w, hwπ, hw⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_normalized_fourier_oscillator hNondiscrete n ψ hu hc hn
  have hwH : w ∈ H := by
    intro f
    let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
      NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
    apply Subtype.ext
    funext x
    rw [hw]
    change _ = conj ((w.val.2 f).val (r • x))
    rw [hw]
    exact QuarterTurnStructure.Construction.fourier_quarterTurnStructure r hr ψ hu (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) f x
  have hU (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : (NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B).val ∈ H := by
    intro f
    exact QuarterTurnStructure.Construction.quarterTurnStructure_quadratic r hr ψ hu (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) B.val f
  have hsurj := BareGeneration.Construction.subgroup_projection_surjective_of_quadratic_weyl hNondiscrete ψ hu hc H hU w hwH hwπ
  have hder : commutator (FunctionsMetaplectic.Construction.Oscillator k n ψ) ≤ H :=
    BareGeneration.Construction.commutator_le_of_central_kernel (OscillatorProjection.Construction.oscillatorProjection k n ψ) H
      (fun x => by
        have h : OscillatorProjection.Construction.oscillatorProjection k n ψ x ∈ H.map (OscillatorProjection.Construction.oscillatorProjection k n ψ) := by rw [hsurj]; trivial
        exact h)
      (BareGeneration.Construction.nonarchimedean_oscillator_kernel_central hNondiscrete ψ hu hc hn)
  change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) ≤ H
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · apply hder
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure hx
  · obtain rfl := Set.mem_singleton_iff.mp hx
    intro f
    exact (QuarterTurnStructure.Construction.quarterTurnStructure_neg r hr f).symm

theorem nonarchimedean_metaplectic_kernel_sign_of_sqrt_neg_one
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (r : k) (hr : r ^ 2 = -1) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.val.2 f = ε • f := by
  obtain ⟨z, hz, hscalar⟩ := BruhatCosets.Construction.nonarchimedean_oscillator_kernel_unit_scalar hNondiscrete ψ hu hc hn a.val ha
  have hcomm := nonarchimedean_metaplectic_le_quarterTurnSubgroup hNondiscrete n ψ hu hc hn r hr a.property
  by_cases he : ∃ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, f ≠ 0
  · obtain ⟨f, hf⟩ := he
    obtain ⟨y, hy⟩ : ∃ y, f.val y ≠ 0 := by
      by_contra! h
      exact hf (Subtype.ext (funext h))
    have hh := hcomm f
    rw [hscalar, hscalar, QuarterTurnStructure.Construction.quarterTurnStructure_smul] at hh
    have hv := congrArg (fun g : FunctionsMetaplectic.Construction.schwartzBruhat k n => g.val ((-r) • y)) hh
    have hxy : r • ((-r) • y) = y := by
      rw [smul_smul, mul_neg, ← pow_two, hr, neg_neg, one_smul]
    change z * conj (f.val (r • ((-r) • y))) = conj z * conj (f.val (r • ((-r) • y))) at hv
    rw [hxy] at hv
    have hreal : z = conj z := mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hy) hv
    refine ⟨z, ?_, hscalar⟩
    calc
      z ^ 2 = z * conj z := by rw [← hreal, pow_two]
      _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  · refine ⟨1, one_pow 2, fun f => ?_⟩
    have hf : f = 0 := by by_contra h; exact he ⟨f, h⟩
    rw [hf, map_zero, smul_zero]

theorem nonarchimedean_metaplectic_same_projection_sign_of_sqrt_neg_one
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (r : k) (hr : r ^ 2 = -1) (a b : FunctionsMetaplectic.Construction.Metaplectic k n ψ)
    (hab : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = FunctionsMetaplectic.Construction.metaplecticProjection k n ψ b) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
      FunctionsMetaplectic.Construction.weilRepresentation k n ψ a f = ε • FunctionsMetaplectic.Construction.weilRepresentation k n ψ b f := by
  have hker : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨ε, hε, h⟩ := nonarchimedean_metaplectic_kernel_sign_of_sqrt_neg_one hNondiscrete ψ hu hc hn
    r hr (a * b⁻¹) hker
  refine ⟨ε, hε, fun f => ?_⟩
  have hh := h (b.val.val.2 f)
  change a.val.val.2 (b.val.val.2.symm (b.val.val.2 f)) = ε • b.val.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using! hh

end

end OAI.RepresentationTheory.Weil.Local.QuarterTurnKernel.Construction
