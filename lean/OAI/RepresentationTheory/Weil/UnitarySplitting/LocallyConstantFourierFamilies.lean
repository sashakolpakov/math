import OAI.RepresentationTheory.Weil.UnitarySplitting.CompactLocallyConstantFamilies
import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierPairing

/-! # Locally Constant Fourier Families -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.LocallyConstantFourierFamilies.Construction

noncomputable section

/-! Compact Fourier amplitudes vary locally constantly when their phase
and invertible frequency coordinates vary continuously. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem locallyConstant_weighted_homeomorph_family
    {P X : Type} [TopologicalSpace P] [NormedAddCommGroup X] [ProperSpace X]
    (L : P → X ≃ₜ X) (hL : Continuous (fun z : P × X => L z.1 z.2))
    (hLi : Continuous (fun z : P × X => (L z.1).symm z.2))
    (a : P × X → ℂ) (ha : IsLocallyConstant a)
    (f : X → ℂ) (hfl : IsLocallyConstant f) (hfs : HasCompactSupport f) :
    IsLocallyConstant (fun p : P => fun x : X => a (p, x) * f (L p x)) := by
  apply CompactLocallyConstantFamilies.Construction.locallyConstant_family_of_local_compact_support _ (ha.mul (hfl.comp_continuous hL))
  intro p
  obtain ⟨T, hT, he⟩ := CompactLocallyConstantFamilies.Construction.compact_pullback_family_local_support L hLi (tsupport f) hfs p
  refine ⟨T, hT, ?_⟩
  filter_upwards [he] with t ht x hx
  change a (t, x) * f (L t x) = 0
  rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (ht x hh)), mul_zero]

def chirpedBilinearFourierFamily
    {F V P : Type} [Field F] [AddCommGroup V] [Module F V] [MeasurableSpace V]
    (ψ : AddChar F ℂ) (μ : Measure V) (B : LinearMap.BilinForm F V)
    (q : P × V → F) (L : P → V → V) (C : V → ℂ) (p : P) (v : V) : ℂ :=
  ψ (q (p, v)) * ∫ x, ψ (B (L p v) x) * (ψ (q (p, x)) * C x) ∂μ

theorem chirpedBilinearFourierFamily_locallyConstant
    {F V P : Type} [NontriviallyNormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [IsUltrametricDist F]
    [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V] [ProperSpace V]
    [MeasurableSpace V] [BorelSpace V] [TopologicalSpace P] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (e : V ≃L[F] Local.FunctionsMetaplectic.Construction.Position F d)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hn : ∃ x : F, ψ x ≠ 1)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (q : P × V → F) (hq : Continuous q)
    (L : P → V ≃ₜ V) (hL : Continuous (fun z : P × V => L z.1 z.2))
    (hLi : Continuous (fun z : P × V => (L z.1).symm z.2))
    (C : V → ℂ) (hCl : IsLocallyConstant C) (hCs : HasCompactSupport C) :
    IsLocallyConstant (fun p => chirpedBilinearFourierFamily ψ μ B q (fun p => L p) C p) := by
  let a : P × V → ℂ := fun z => ψ (q z)
  have hal : IsLocallyConstant a := (LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hq
  let φ : P → V → ℂ := fun p x => a (p, x) * C x
  have hφ : IsLocallyConstant φ := by
    apply CompactLocallyConstantFamilies.Construction.locallyConstant_family_of_local_compact_support
      (fun z : P × V => a z * C z.2) (hal.mul (hCl.comp_continuous continuous_snd))
    intro p
    refine ⟨tsupport C, hCs, Filter.Eventually.of_forall (fun t x hx => ?_)⟩
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  let φ₀ : V → ℂ := φ p
  have hφ₀l : IsLocallyConstant φ₀ :=
    (hal.comp_continuous (continuous_const.prodMk continuous_id)).mul hCl
  have hφ₀s : HasCompactSupport φ₀ := hCs.mul_left
  let T : V → ℂ := fun v => ∫ x, ψ (B v x) * φ₀ x ∂μ
  obtain ⟨hTl, hTs⟩ := BilinearFourierPairing.Construction.bilinear_fourier_compact_locallyConstant hF e B hB
    (ContinuousLinearEquiv.refl F V) ψ hc hn μ φ₀ hφ₀l hφ₀s
  have ht : IsLocallyConstant (fun t : P => fun v : V => a (t, v) * T (L t v)) :=
    locallyConstant_weighted_homeomorph_family L hL hLi a hal T hTl hTs
  filter_upwards [hφ.eventually_eq p, ht.eventually_eq p] with t hφt ht
  funext v
  calc
    _ = a (t, v) * T (L t v) := by
      unfold chirpedBilinearFourierFamily
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ψ (B (L t v) x) * φ t x = ψ (B (L t v) x) * φ p x
        rw [hφt]
    _ = a (p, v) * T (L p v) := congrFun ht v
    _ = _ := rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.LocallyConstantFourierFamilies.Construction
