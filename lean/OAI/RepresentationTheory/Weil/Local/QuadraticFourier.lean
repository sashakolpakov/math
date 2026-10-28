import OAI.RepresentationTheory.Weil.Local.FourierTensor

/-! # Quadratic Fourier -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticFourier.Construction

noncomputable section

section

/-! Completing the square in compact local Gaussian integrals. -/

open _root_.MeasureTheory
open scoped Classical

def compactQuadraticFunction
    {k : Type} [Field k] (ψ : AddChar k ℂ) (U : Set k) (a : k) : k → ℂ :=
  U.indicator (fun x => ψ (a * x ^ 2 / 2))

theorem scalarFourier_compactQuadratic
    {k : Type} [NormedField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup k) (a z : k) (hz : z ∈ U) :
    FourierTensor.Construction.scalarFourierIntegral ψ μ (compactQuadraticFunction ψ U a) (a * z) =
      ψ (-(a * z ^ 2 / 2)) * ∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂μ := by
  unfold FourierTensor.Construction.scalarFourierIntegral
  rw [← integral_add_right_eq_self
    (fun y => compactQuadraticFunction ψ U a y * ψ (-(a * z * y))) z,
    ← integral_indicator U.isOpen.measurableSet, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hymem : y + z ∈ U ↔ y ∈ U := U.add_mem_cancel_right hz
    by_cases hy : y ∈ U
    · simp only [compactQuadraticFunction, Set.indicator_of_mem hy,
        Set.indicator_of_mem (hymem.mpr hy)]
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      have h2 : (2 : k) ≠ 0 := by norm_num
      field_simp
      ring
    · have hyz : y + z ∉ U := fun h => hy (hymem.mp h)
      simp [compactQuadraticFunction, hy, hyz]

theorem compactQuadratic_translation
    {k : Type} [NormedField k] [CharZero k]
    (ψ : AddChar k ℂ) (U : OpenAddSubgroup k) (a t : k) (ht : t ∈ U)
    (hphase : ψ (a * t ^ 2 / 2) = 1)
    (hpair : ∀ y ∈ U, ψ (a * y * t) = 1) :
    ∀ y, compactQuadraticFunction ψ U a (y + t) = compactQuadraticFunction ψ U a y := by
  intro y
  have hymem : y + t ∈ U ↔ y ∈ U := U.add_mem_cancel_right ht
  by_cases hy : y ∈ U
  · simp only [compactQuadraticFunction, Set.indicator_of_mem hy,
      Set.indicator_of_mem (hymem.mpr hy)]
    have hsplit : a * (y + t) ^ 2 / 2 = a * y ^ 2 / 2 + a * y * t + a * t ^ 2 / 2 := by
      have h2 : (2 : k) ≠ 0 := by norm_num
      field_simp
      ring
    rw [hsplit, ψ.map_add_eq_mul, ψ.map_add_eq_mul, hphase, hpair y hy, mul_one, mul_one]
  · have hyt : y + t ∉ U := fun h => hy (hymem.mp h)
    simp [compactQuadraticFunction, hy, hyt]

end

/-! Scalar annihilators for compact local Gaussian calculations. -/

open _root_.MeasureTheory
open scoped Classical

def scalarAnnihilator
    {k : Type} [Field k] (ψ : AddChar k ℂ) (U : AddSubgroup k) : AddSubgroup k where
  carrier := {x | ∀ y ∈ U, ψ (x * y) = 1}
  zero_mem' := by simp
  add_mem' {x z} hx hz y hy := by rw [add_mul, ψ.map_add_eq_mul, hx y hy, hz y hy, one_mul]
  neg_mem' {x} hx y hy := by rw [neg_mul, ψ.map_neg_eq_inv, hx y hy, inv_one]

theorem integral_scalarPairing_subgroup
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup k) (z : k) :
    (∫ y in (U : Set k), ψ (z * y) ∂μ) =
      if z ∈ scalarAnnihilator ψ U.toAddSubgroup then (μ.real (U : Set k) : ℂ) else 0 := by
  let χ : AddChar k ℂ := ψ.compAddMonoidHom (LinearMap.mulLeft k z).toAddMonoidHom
  exact CompactCharacter.Construction.integral_character_subgroup μ U χ

theorem scalarAnnihilator_compact_open
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (U : OpenAddSubgroup k) (hU : IsCompact (U : Set k)) :
    IsCompact (scalarAnnihilator ψ U.toAddSubgroup : Set k) ∧
      IsOpen (scalarAnnihilator ψ U.toAddSubgroup : Set k) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let e := ContinuousLinearEquiv.funUnique (Fin 1) k k
  let U₁ := U.comap e.toLinearEquiv.toAddEquiv.toAddMonoidHom e.continuous
  have hU₁ : IsCompact (U₁ : Set (FunctionsMetaplectic.Construction.Position k 1)) := e.toHomeomorph.isCompact_preimage.mpr hU
  let μ : Measure (FunctionsMetaplectic.Construction.Position k 1) := Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k))
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  obtain ⟨hcomp, hopen⟩ := CompactCharacter.Construction.additiveAnnihilator_compact_open hNondiscrete ψ hu hc hn μ U₁ hU₁
  have hset : (scalarAnnihilator ψ U.toAddSubgroup : Set k) =
      e.symm ⁻¹' (CompactCharacter.Construction.additiveAnnihilator ψ U₁.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k 1)) := by
    ext x
    change (∀ y ∈ U, ψ (x * y) = 1) ↔
      ∀ y : FunctionsMetaplectic.Construction.Position k 1, y ∈ U₁ → ψ (FunctionsMetaplectic.Construction.dot (e.symm x) y) = 1
    constructor
    · intro hx y hy
      have hy₀ : y 0 ∈ U := hy
      simpa [FunctionsMetaplectic.Construction.dot, e, Fin.sum_univ_one] using hx (y 0) hy₀
    · intro hx y hy
      have h := hx (fun _ => y) hy
      simpa [FunctionsMetaplectic.Construction.dot, e, Fin.sum_univ_one] using h
  rw [hset]
  exact ⟨e.symm.toHomeomorph.isCompact_preimage.mpr hcomp, hopen.preimage e.symm.continuous⟩

theorem scalarFourier_translate
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (f : k → ℂ) (t x : k) :
    FourierTensor.Construction.scalarFourierIntegral ψ μ (fun y => f (y + t)) x =
      ψ (x * t) * FourierTensor.Construction.scalarFourierIntegral ψ μ f x := by
  let μ₁ : Measure (FunctionsMetaplectic.Construction.Position k 1) := Measure.pi (fun _ : Fin 1 => μ)
  let : μ₁.IsAddHaarMeasure := by dsimp [μ₁]; infer_instance
  have h := CompactCharacter.Construction.fourierIntegral_translate ψ μ₁ (fun y => f (y 0)) (fun _ => t) (fun _ => x)
  change FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) (fun y => f (y 0 + t)) (fun _ => x) =
    ψ (FunctionsMetaplectic.Construction.dot (fun _ : Fin 1 => x) (fun _ => t)) *
      FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) (fun y => f (y 0)) (fun _ => x) at h
  rw [NonarchimedeanHaar.Construction.fourierIntegral_singleton_position ψ μ (fun y => f (y + t)),
    NonarchimedeanHaar.Construction.fourierIntegral_singleton_position ψ μ f] at h
  simpa only [FunctionsMetaplectic.Construction.dot, Fin.sum_univ_one, FourierTensor.Construction.scalarFourierIntegral] using! h

theorem scalarFourier_vanishes_of_translation
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (f : k → ℂ) (t x : k) (ht : ∀ y, f (y + t) = f y) (hx : ψ (x * t) ≠ 1) :
    FourierTensor.Construction.scalarFourierIntegral ψ μ f x = 0 := by
  have h := scalarFourier_translate ψ μ f t x
  have heq : (fun y => f (y + t)) = f := funext ht
  rw [heq] at h
  by_contra hn
  apply hx
  apply mul_right_cancel₀ hn
  simpa using h.symm

end

end OAI.RepresentationTheory.Weil.Local.QuadraticFourier.Construction
